#!/usr/bin/env node

import fs from 'node:fs'
import path from 'node:path'

function fail(message) {
  console.error(message)
  process.exit(1)
}

const args = Object.fromEntries(
  process.argv.slice(2).reduce((pairs, value, index, values) => {
    if (value.startsWith('--') && values[index + 1] && !values[index + 1].startsWith('--')) {
      pairs.push([value.slice(2), values[index + 1]])
    }
    return pairs
  }, []),
)

const revision = args.revision
const receiptPath = args.receipt
const kustomizationPath = args.kustomization
if (!revision || !receiptPath || !kustomizationPath) {
  fail('usage: promote-production.mjs --revision SHA --receipt FILE --kustomization FILE')
}
if (!/^[0-9a-f]{40}$/.test(revision)) fail('revision must be a full lowercase Git SHA')

let receipt
try {
  receipt = JSON.parse(fs.readFileSync(receiptPath, 'utf8'))
} catch {
  fail('build receipt must be valid JSON')
}
if (JSON.stringify(Object.keys(receipt).sort()) !== JSON.stringify(['images', 'revision', 'version'])) {
  fail('unexpected build receipt fields')
}
if (receipt.version !== 1 || receipt.revision !== revision) fail('build receipt revision mismatch')
if (!receipt.images || Object.keys(receipt.images).length !== 1 || !receipt.images.web) {
  fail('build receipt must contain only the web image')
}
const imageMatch = receipt.images.web.match(
  /^ghcr\.io\/q5m-ai\/causal-set-emergence@(sha256:[0-9a-f]{64})$/,
)
if (!imageMatch) fail('build receipt image must be the digest-addressed Causal Set Emergence image')

const resolved = path.resolve(kustomizationPath)
let source = fs.readFileSync(resolved, 'utf8')
const digestPattern = /(newName: ghcr\.io\/q5m-ai\/causal-set-emergence\n\s+digest: )sha256:[0-9a-f]{64}/g
const releasePattern = /(q5m\.ai\/release: )[0-9a-f]{40}/g
if ([...source.matchAll(digestPattern)].length !== 1) fail('expected one production image digest')
if ([...source.matchAll(releasePattern)].length !== 1) fail('expected one production release annotation')
source = source.replace(digestPattern, `$1${imageMatch[1]}`).replace(releasePattern, `$1${revision}`)
fs.writeFileSync(resolved, source)

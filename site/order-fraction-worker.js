// Disposable browser worker running a pinned Pyodide build.
const PYODIDE_BASE = "https://cdn.jsdelivr.net/pyodide/v0.28.3/full/";

importScripts(`${PYODIDE_BASE}pyodide.js`);

const runtime = loadPyodide({ indexURL: PYODIDE_BASE });

runtime
  .then(() => self.postMessage({ type: "ready" }))
  .catch(error => self.postMessage({ type: "boot-error", error: error.stack || String(error) }));

self.addEventListener("message", async event => {
  if (event.data?.type !== "run") return;

  try {
    const python = await runtime;
    python.setStdout({ batched: line => self.postMessage({ type: "line", line }) });
    python.setStderr({ batched: line => self.postMessage({ type: "line", line }) });
    await python.runPythonAsync(event.data.source);
    self.postMessage({ type: "done" });
  } catch (error) {
    self.postMessage({ type: "run-error", error: error.stack || String(error) });
  }
});

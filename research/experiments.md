# Experimental feasibility — outcome B

**B. The exact missing model-to-observable calculation.** No major experiment
is proposed. This bounded assessment is separate from the mathematical release
and from #24's closure criterion. It does not claim a no-go for all causal-set
models, or a new empirical constraint.

## 1. Search and model selection

Search date: **16 October 2026**. Primary papers and official archive pages,
not general quantum-gravity publicity, were inspected. A bounded INSPIRE search
used `title "causal set" and date > 2024` (12 records), a diffusion query
(5 records), a Belenchia/Sorkin nonlocal query (6 records), and the 12 most
recent of 16 indexed citations to DHS below. Relevant full texts were read at
the passages listed here. An initial unquoted search was noisy and was not
used to assert completeness; arXiv's search API returned HTTP 429. This is
neither exhaustive literature coverage nor proof that no suitable model exists.
Versions, retrieval hashes and queries are in [evidence.json](evidence.json).

| Primary source / inspected passages | Specified dynamics and observable | Limitation relevant here |
| --- | --- | --- |
| **DHS:** Dowker–Henson–Sorkin, [1009.3058v2](https://arxiv.org/html/1009.3058v2), §§2–4, (16)–(21), (70) | Fixed Poisson-sprinkled 4D Minkowski background; classical massless scalar retarded link kernel. An oscillating source path couples with charge q; a finite detector sums its field. Mean and variance of the detector output are calculated | Not dynamical gravity or a full electromagnetic model; source/detector embedding is externally specified. Ordinary dispersion and coherence survive in this model |
| **PDS:** Philpott–Dowker–Sorkin, [0810.5591v2](https://arxiv.org/html/0810.5591v2), §§II–VI, (36), (43)–(49) | Intrinsic massive-particle swerves motivate a Lorentz-invariant diffusion model. The massless kinetic equation has independent energy diffusion and drift parameters; it predicts spectral distortion | Massless coefficients are phenomenological, not derived from a complete causal-set gravity/matter law. Particle trajectories remain null; this is not a time-of-flight anomaly |
| Belenchia–Benincasa–Liberati, [1411.6513v2](https://arxiv.org/html/1411.6513v2), abstract, scalar equations and quantization discussion | Nonlocal scalar field dynamics from causal-set-inspired operators; nonlocal scale and propagator must be specified | An additional matter/operator choice, not the unsmeared gravitational action's continuum limit and not a derived photon or graviton detector response |
| Mentasti–Nasiri, [2505.24620v1](https://arxiv.org/html/2505.24620v1), §§1, 3–6 | Covariant massless diffusion in an expanding universe; conditional LISA spectral forecasts for cosmological stochastic backgrounds | Forecast, not a detection or current bound. §1 explicitly says the missing field-level diffusion prevents applying this particle calculation directly to resolved LIGO binary events |
| Kastrati, [2608.18753v1](https://arxiv.org/html/2608.18753v1), §§II–IV, VI | A particular 1+1D link-exponential propagator yields an effective curvature coupling 1/6 at leading curvature order | Recent primary work showing that a specified matter kernel matters; not a 3+1D Maxwell prediction or validation of our gravitational obstruction |

The strongest **concrete source-to-detector** candidate found is DHS. In its
fundamental units, L(e′,e) is κ when e≺e′ is a link and zero otherwise; the
observable is `F = q * sum_source sum_detector L`. Its mean uses the empty
interval probability `exp(-V)`, **not** the signed BDG polynomial times that
probability. Its variance requires correlated link/interval-union probabilities.
Thus replacing its kernel with our action kernel would change the model.

No inspected source supplies a combined causal-set gravitational dynamics,
physical electromagnetic/gravitational matter coupling and astrophysical
likelihood whose signal is fixed by CO, FLAT or SW.

## 2. Does this repository inform a prediction?

**Yes as a consistency warning and analytic method; not as a signal amplitude.**
CO says that one unsmeared *mean gravitational action* does not approach its
proposed geometric target on a particular fixed compact curved background.
It gives neither equations selecting an observed lens spacetime nor a photon
or gravitational-wave Green function. That slab is not established as a
solution of a selected gravity/matter theory or an astrophysical lens.
A density-asymptotic divergence is not a finite-density speed, damping rate,
random walk, or detectable phase shift. Even differentiating a limiting action
to get field equations would require additional uniform control.

The physical-interval and full-partner methods could test a **chosen** matter
kernel on curved backgrounds. They cannot identify different kernels, equate
a mean inverse with the inverse mean, or infer connected fluctuations from a
one-point expectation. PDS's diffusion/drift parameters and a nonlocal scalar
length are not determined by our theorems. Smearing is a different observable,
not an automatic fix justified by this package.

## 3. Quantitative scale check before experiment design

Run `python3 research/estimate_signals.py`. Every number below is a conditional
scale or a cited model bound, **not a BDG-derived prediction**.

- **DHS scalar signal:** inserting its deliberately restrictive AGN example
  into (70), with distance 10^60, duration 10^27, area 10^52, detector depth
  10^26 and source velocity 0.1 in its fundamental units, gives fractional
  RMS upper scale **8.94×10⁻¹³**. This is an approximate bound in that model,
  not a guaranteed nonzero effect or a general Maxwell noise floor. DHS finds
  no changed dispersion. It does not support a large astronomical blur signal.
- **PDS/CMB:** published separate-parameter bounds are approximately
  **k₁<3×10⁻⁴⁴ J/s** when k₂=0 and **|k₂|<10⁻⁴³ J/s** when k₁=0,
  using a 50-parts-per-million blackbody-deviation criterion; joint bounds
  are correlated. At 160 GHz over an illustrative 4.35×10^17 seconds,
  k₁t/E and |k₂|t/E at these bounds are **1.23×10⁻⁴** and **4.10×10⁻⁴**.
  These are transport strengths, not post-fit intensity residuals. Temperature
  refitting, expansion and foregrounds must be included in an actual constraint.
- **Stochastic GW alternative:** the LISA paper forecasts sensitivity near
  **10⁻⁵⁶ J/s** for favorable cosmological spectra. At 1 mHz the same dimensional
  ratio is **0.00657**. This explains the low-frequency leverage; it is not a
  measured limit, an identification of coefficient conventions across papers,
  or usable LISA observational data today.
- **Timing comparison only:** for the *invented comparator*
  `|delta v|/c = (E/E_Pl)^n`, 30 GeV over 1 Gpc gives **0.253 s** for n=1
  and **6.21×10⁻¹⁹ s** for n=2, ignoring redshift. Neither law follows from
  causal-set discreteness. For a common-path-canceling lens differential with
  30-day path-delay scale, the corresponding linear values are **2.12×10⁻²² s**
  at 1 eV and **6.37×10⁻¹² s** at 30 GeV. Cancellation of source lag can also
  cancel most propagation leverage; a full lens response must be derived.

## 4. Data, constraints and systematic floors

Official entries below returned HTTP 200 at this assessment. Only the **2,388-byte
FIRAS table** and small documentation/catalogue responses were downloaded for
inspection; no strain, event-list or light-curve bulk downloads or fits were run.
Availability is not proof that a likelihood is ready.

| Route / usable public input | Existing sensitivity or constraint | Systematics and decision |
| --- | --- | --- |
| **CMB spectral distortion — strongest immediately usable phenomenological alternative.** [NASA FIRAS monopole table](https://lambda.gsfc.nasa.gov/data/cobe/firas/monopole_spec/firas_monopole_spec_v1.txt) and [column/calibration documentation](https://lambda.gsfc.nasa.gov/product/cobe/firas_monopole_spect.html) | Verified 43 frequency bins, 2.27–21.33 cm⁻¹ (68.1–639.5 GHz); intensities, residuals, 1σ errors and Galactic template. Peak bin error is **46.9 ppm**, consistent in scale with the historical 50 ppm criterion | Temperature degeneracy, calibration, Galactic foreground subtraction and inter-bin covariance. The table is not a full covariance likelihood. A re-fit would constrain free diffusion parameters, not our action theorem or causal sets uniquely |
| **Multi-messenger timing.** [GWOSC GW170817 v3](https://gwosc.org/eventapi/html/GWTC-1-confident/GW170817/v3/) lists H1/L1/V1 strain, quality bits and parameter products; [Fermi LAT public access](https://fermi.gsfc.nasa.gov/ssc/data/access/lat/) supplies photon/spacecraft queries. [GBM GRB090510 directory](https://heasarc.gsfc.nasa.gov/FTP/fermi/data/gbm/bursts/2009/bn090510016/current/) lists TTE and response files | [Abbott et al. 1710.05834v2](https://arxiv.org/abs/1710.05834v2): GW170817/GRB170817A delay **1.74±0.05 s**, inferred speed-difference interval **−3×10⁻¹⁵ to +7×10⁻¹⁶** times c under stated emission assumptions. [Vasileiou et al. 1305.3463v1](https://arxiv.org/abs/1305.3463v1): strongest subluminal linear LIV scale **>7.6 E_Pl**, quadratic **>1.3×10¹¹ GeV**, 95%, when not allowing source-intrinsic dispersion | Intrinsic emission delay/spectral evolution, redshift, selection and timing/energy response dominate interpretation. The 0.05 s measurement error is not an emission-lag bound. At 40 Mpc, 1.74 s/light-time is 4.23×10⁻¹⁶, not by itself a measured speed difference. GBM is not a substitute for the LAT sample in the cited LIV analysis. These are comparator constraints, not causal-set constraints; no claim they are today's strongest |
| **Strong lensing / repeated-image differential timing.** [CDS J/A+A/640/A105](https://cdsarc.cds.unistra.fr/viz-bin/cat/J/A+A/640/A105), with checked [ReadMe](https://cdsarc.cds.unistra.fr/ftp/J/A+A/640/A105/ReadMe): R-band light curves for 23 quasars, observation times, magnitudes and errors | [Millon et al. 2002.05736v2](https://arxiv.org/html/2002.05736v2): delays in 18 systems, nine with a delay precision better than 15%. These are optical light curves, not a coincident lensed multi-messenger sample | Cadence/season gaps, intrinsic variability, microlensing, source-size chromatic effects, lens mass-sheet/environment degeneracy and macro delay modeling. A 1-day error on a 30-day delay is already 3%; this is an illustrative floor, not a universal survey bound. No derived causal-set lens perturbation can be compared. **Do not prioritize over spectral alternatives** merely because CO involves focusing |
| **Future stochastic GW spectra** | Conditional LISA forecast above; no LISA science data used | Cosmological source-shape uncertainty, confusion foregrounds, instrument noise and transfer function. Not a resolved-event PDS test; not grounds for commissioning a major experiment |

The direct COSMOGRAIL site failed TLS access; the CDS catalogue and its schema
were successfully checked instead. The official archive evidence and the primary
papers establish usable starting points, not a novel sensitivity result.

For orientation the homogeneous PDS kinetic equation (36), with f the
number density per energy, is

```math
\partial_t f=-(k_1+k_2)\partial_E f+k_1E\partial_E^2 f.
```

This keeps propagation null. Expansion adds the redshift term in PDS (49);
the phase-space convention and dilution must be carried consistently. Simply
calling k₁ a variance per unit time or copying it into a wave equation is
not a derivation.

## 5. Exact missing calculation and bounded next step

Before a model-specific empirical test can be proposed, supply:

1. **A model, not just an action:** a specified causal-set ensemble/dynamical
   law, density and any smearing/nonlocality scale; a scalar, electromagnetic
   or gravitational matter operator, state, curvature coupling, and source and
   detector coupling. A fixed Poisson background is a permissible *test model*,
   but must not be called a solution of quantum causal-set gravity.
2. **Its observable response:** construct the retarded propagator on that
   ensemble and the detector functional. Calculate the difference of its mean
   from the matched continuum response and its connected covariance at **finite
   density**, with physical interval unions and the actual source/detector
   windows. For lensing or multi-messenger use a real lens/cosmological geometry,
   not the CO slab by analogy. Include normalization and nuisance parameters.
3. **The link to our result:** show whether CO's surviving term enters that
   propagator/field operator or changes the background selected by the dynamics.
   If not, report zero relevance to that prediction rather than assigning the
   action's exponent to a dispersion coefficient. Derive any map to k₁, k₂ or
   a nonlocality scale; the current mathematics supplies none.
4. **A likelihood and numerical comparison:** fold the response through the
   verified archive's timing/spectral/strain response, covariance and source
   uncertainties; compare to published bounds. State a nonzero allowed signal
   range and its systematic floor before claiming a falsifiable parameter test.

**Smallest next theoretical calculation:** on a chosen fixed curved background,
apply DHS's link kernel (not K₄) to compact smooth source and detector windows;
compute the continuum-subtracted mean and the two-link connected integral using
physical interval **unions**, then compare with its Minkowski limit. This is a
scalar model diagnostic, not yet an astronomical proposal. A separate explicit
model is required to connect it to BDG dynamics. Stop if that connection cannot
be made. No paid compute, new observing programme or outreach is warranted by
this assessment.

A mathematical counterexample rejects a quantified correspondence claim.
Model falsification rejects a specified physical model/parameter range against
data. Empirical support would require a discriminating prediction surviving
competing explanations. None of those three statements implies the others.

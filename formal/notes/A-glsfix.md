# A-glsfix: GLSPass.lean under autoImplicit=false, and a sweep of Mathlib-free Formal/Core

STATUS: in progress (probe GLSFix, 2026-10-29).

Plan: (1) bind `d` in `skew_fval` explicitly; re-check GLSPass with check.sh (-DautoImplicit=false).
(2) re-check every Mathlib-free module under Formal/Core in dependency order; fix statement-preserving.

/-
Copyright (c) 2026 Ravi Hegde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ravi Hegde
-/
module

public import GSTC.Scattering.Susceptibility

open scoped Matrix

public section

namespace GSTC.Scattering

@[expose] noncomputable def couplingVPar (cfg : Config) (s : Side)
    (sus : Susceptibilities) (w : Wave) : Ten2 :=
  (1 / 2 : ℂ) • ((cfg.vac.eps0 : ℂ) • (chiTT sus.ee)
      + (1 / (cfg.vac.c0 : ℂ)) • ((PropDir.sign (Wave.dir s w) : ℂ)
          • (chiTT sus.em * (ncross * waveY (Wave.medium cfg s w) cfg.kPar))))
    + (1 / 2 : ℂ) • (-((PropDir.sign (Wave.dir s w) : ℂ))
        / ((cfg.omega : ℂ) * (zTM (Wave.medium cfg s w) cfg.kPar : ℂ)))
        • (outer (chiTN sus.ee) (kVec cfg.kPar))
    + (1 / 2 : ℂ) • (1 / ((cfg.omega : ℂ) * (cfg.vac.eta0 : ℂ)))
        • (outer (chiTN sus.em) (lVec cfg.kPar))

@[expose] noncomputable def couplingVN (cfg : Config) (s : Side)
    (sus : Susceptibilities) (w : Wave) : Row2 :=
  (1 / 2 : ℂ) • ((cfg.vac.eps0 : ℂ) • (chiNT sus.ee)
      + (1 / (cfg.vac.c0 : ℂ)) • ((PropDir.sign (Wave.dir s w) : ℂ)
          • (chiNT sus.em * (ncross * waveY (Wave.medium cfg s w) cfg.kPar))))
    + (1 / 2 : ℂ) • (-((PropDir.sign (Wave.dir s w) : ℂ))
        / ((cfg.omega : ℂ) * (zTM (Wave.medium cfg s w) cfg.kPar : ℂ)))
        • ((chiNN sus.ee) • (kRow cfg.kPar))
    + (1 / 2 : ℂ) • (1 / ((cfg.omega : ℂ) * (cfg.vac.eta0 : ℂ)))
        • ((chiNN sus.em) • (lRow cfg.kPar))

@[expose] noncomputable def couplingWPar (cfg : Config) (s : Side)
    (sus : Susceptibilities) (w : Wave) : Ten2 :=
  (1 / 2 : ℂ) • ((1 / (cfg.vac.c0 : ℂ)) • (chiTT sus.me)
      + (cfg.vac.mu0 : ℂ) • ((PropDir.sign (Wave.dir s w) : ℂ)
          • (chiTT sus.mm * (ncross * waveY (Wave.medium cfg s w) cfg.kPar))))
    + (1 / 2 : ℂ) • (-((PropDir.sign (Wave.dir s w) : ℂ)) * (cfg.vac.eta0 : ℂ)
        / ((cfg.omega : ℂ) * (zTM (Wave.medium cfg s w) cfg.kPar : ℂ)))
        • (outer (chiTN sus.me) (kVec cfg.kPar))
    + (1 / 2 : ℂ) • (1 / (cfg.omega : ℂ))
        • (outer (chiTN sus.mm) (lVec cfg.kPar))

@[expose] noncomputable def couplingWN (cfg : Config) (s : Side)
    (sus : Susceptibilities) (w : Wave) : Row2 :=
  (1 / 2 : ℂ) • ((1 / (cfg.vac.c0 : ℂ)) • (chiNT sus.me)
      + (cfg.vac.mu0 : ℂ) • ((PropDir.sign (Wave.dir s w) : ℂ)
          • (chiNT sus.mm * (ncross * waveY (Wave.medium cfg s w) cfg.kPar))))
    + (1 / 2 : ℂ) • (-((PropDir.sign (Wave.dir s w) : ℂ)) * (cfg.vac.eta0 : ℂ)
        / ((cfg.omega : ℂ) * (zTM (Wave.medium cfg s w) cfg.kPar : ℂ)))
        • ((chiNN sus.me) • (kRow cfg.kPar))
    + (1 / 2 : ℂ) • (1 / (cfg.omega : ℂ))
        • ((chiNN sus.mm) • (lRow cfg.kPar))

end GSTC.Scattering

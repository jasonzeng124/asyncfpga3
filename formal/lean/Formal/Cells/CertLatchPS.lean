import Formal.Cells.CertLatchPS.B00
import Formal.Cells.CertLatchPS.B01
import Formal.Cells.CertLatchPS.B02
import Formal.Cells.CertLatchPS.B03
import Formal.Cells.CertLatchPS.B04
import Formal.Cells.CertLatchPS.B05
import Formal.Cells.CertLatchPS.B06
import Formal.Cells.CertLatchPS.B07
import Formal.Cells.CertLatchPS.B08
import Formal.Cells.CertLatchPS.B09
import Formal.Cells.CertLatchPS.B10
import Formal.Cells.CertLatchPS.B11
import Formal.Cells.CertLatchPS.B12
import Formal.Cells.CertLatchPS.B13
import Formal.Cells.CertLatchPS.B14
import Formal.Cells.CertLatchPS.B15
import Formal.Cells.CertLatchPS.B16
import Formal.Cells.CertLatchPS.B17
import Formal.Cells.CertLatchPS.B18
import Formal.Cells.CertLatchPS.B19
import Formal.Cells.CertLatchPS.B20
import Formal.Cells.CertLatchPS.B21
import Formal.Cells.CertLatchPS.B22
import Formal.Cells.CertLatchPS.B23
import Formal.Cells.CertLatchPS.B24
import Formal.Cells.CertLatchPS.B25
import Formal.Cells.CertLatchPS.B26
import Formal.Cells.CertLatchPS.B27
import Formal.Cells.CertLatchPS.B28
import Formal.Cells.CertLatchPS.B29
import Formal.Cells.CertLatchPS.B30
import Formal.Cells.CertLatchPS.B31
import Formal.Cells.CertLatchPS.B32
import Formal.Cells.CertLatchPS.B33
import Formal.Cells.CertLatchPS.B34
import Formal.Cells.CertLatchPS.B35
import Formal.Cells.CertLatchPS.B36
import Formal.Cells.CertLatchPS.B37
import Formal.Cells.CertLatchPS.B38
import Formal.Cells.CertLatchPS.B39
import Formal.Cells.CertLatchPS.B40
import Formal.Cells.CertLatchPS.B41

/-!
# Formal.Cells.CertLatchPS — hold certificates for 112 of the 185 RaceTablePS rows (GENERATED)

Each certificate: the storage node's own flip as the cause, its episode path's LUT steps as rows, the fewest static
premises; all checked by `CertPS.certOK` (kernel decide). With `CertPS.cert_sound`, in every behaviour each listed
node's acknowledge source keeps its value for the path's summed lower window ends after the node's flip, given the
premises. Skipped (no certificate from the dump used): 0 rows: .
Left out (one certificate spans more netlist chunks than one kernel check fits in memory here): .
-/

namespace Formal.Cells.CertLatchPS
open Formal.Cells.CertPS

set_option maxRecDepth 100000 in
def certs : List (Prem × List CRow) := certs00 ++ certs01 ++ certs02 ++ certs03 ++ certs04 ++ certs05 ++ certs06 ++ certs07 ++ certs08 ++ certs09 ++ certs10 ++ certs11 ++ certs12 ++ certs13 ++ certs14 ++ certs15 ++ certs16 ++ certs17 ++ certs18 ++ certs19 ++ certs20 ++ certs21 ++ certs22 ++ certs23 ++ certs24 ++ certs25 ++ certs26 ++ certs27 ++ certs28 ++ certs29 ++ certs30 ++ certs31 ++ certs32 ++ certs33 ++ certs34 ++ certs35 ++ certs36 ++ certs37 ++ certs38 ++ certs39 ++ certs40 ++ certs41

set_option maxRecDepth 100000 in
theorem certs_ok : certs.all (fun pc => certOK pc.1 pc.2) = true := by
  simp only [certs, List.all_append, certs00_ok, certs01_ok, certs02_ok, certs03_ok, certs04_ok, certs05_ok, certs06_ok, certs07_ok, certs08_ok, certs09_ok, certs10_ok, certs11_ok, certs12_ok, certs13_ok, certs14_ok, certs15_ok, certs16_ok, certs17_ok, certs18_ok, certs19_ok, certs20_ok, certs21_ok, certs22_ok, certs23_ok, certs24_ok, certs25_ok, certs26_ok, certs27_ok, certs28_ok, certs29_ok, certs30_ok, certs31_ok, certs32_ok, certs33_ok, certs34_ok, certs35_ok, certs36_ok, certs37_ok, certs38_ok, certs39_ok, certs40_ok, certs41_ok, Bool.and_self]

set_option maxRecDepth 100000 in
theorem certs_length : certs.length = 112 := by decide

end Formal.Cells.CertLatchPS

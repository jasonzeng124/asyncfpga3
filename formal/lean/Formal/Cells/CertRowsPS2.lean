import Formal.Cells.CertRowsPS2.B00
import Formal.Cells.CertRowsPS2.B01
import Formal.Cells.CertRowsPS2.B02
import Formal.Cells.CertRowsPS2.B03
import Formal.Cells.CertRowsPS2.B04
import Formal.Cells.CertRowsPS2.B05
import Formal.Cells.CertRowsPS2.B06

/-!
# Formal.Cells.CertRowsPS2 — hold certificates for 23 of the 185 RaceTablePS rows (GENERATED)

Each certificate: the storage node's own flip as the cause, its episode path's LUT steps as rows, the fewest static
premises; all checked by `CertPS.certOK` (kernel decide). With `CertPS.cert_sound`, in every behaviour each listed
node's acknowledge source keeps its value for the path's summed lower window ends after the node's flip, given the
premises. Skipped (no certificate from the dump used): 4 rows: SLICE_X4Y54.ALUT.O6, SLICE_X4Y51.ALUT.O6, SLICE_X16Y25.BLUT.O6, SLICE_X16Y18.DLUT.O6.
-/

namespace Formal.Cells.CertRowsPS2
open Formal.Cells.CertPS

set_option maxRecDepth 100000 in
def certs : List (Prem × List CRow) := certs00 ++ certs01 ++ certs02 ++ certs03 ++ certs04 ++ certs05 ++ certs06

set_option maxRecDepth 100000 in
theorem certs_ok : certs.all (fun pc => certOK pc.1 pc.2) = true := by
  simp only [certs, List.all_append, certs00_ok, certs01_ok, certs02_ok, certs03_ok, certs04_ok, certs05_ok, certs06_ok, Bool.and_self]

set_option maxRecDepth 100000 in
theorem certs_length : certs.length = 23 := by decide

end Formal.Cells.CertRowsPS2

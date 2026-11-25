import Formal.Cells.CertRowsPS.B00
import Formal.Cells.CertRowsPS.B01
import Formal.Cells.CertRowsPS.B02
import Formal.Cells.CertRowsPS.B03
import Formal.Cells.CertRowsPS.B04
import Formal.Cells.CertRowsPS.B05
import Formal.Cells.CertRowsPS.B06
import Formal.Cells.CertRowsPS.B07
import Formal.Cells.CertRowsPS.B08
import Formal.Cells.CertRowsPS.B09
import Formal.Cells.CertRowsPS.B10
import Formal.Cells.CertRowsPS.B11
import Formal.Cells.CertRowsPS.B12
import Formal.Cells.CertRowsPS.B13
import Formal.Cells.CertRowsPS.B14
import Formal.Cells.CertRowsPS.B15
import Formal.Cells.CertRowsPS.B16
import Formal.Cells.CertRowsPS.B17
import Formal.Cells.CertRowsPS.B18
import Formal.Cells.CertRowsPS.B19
import Formal.Cells.CertRowsPS.B20
import Formal.Cells.CertRowsPS.B21
import Formal.Cells.CertRowsPS.B22
import Formal.Cells.CertRowsPS.B23
import Formal.Cells.CertRowsPS.B24
import Formal.Cells.CertRowsPS.B25
import Formal.Cells.CertRowsPS.B26
import Formal.Cells.CertRowsPS.B27
import Formal.Cells.CertRowsPS.B28
import Formal.Cells.CertRowsPS.B29
import Formal.Cells.CertRowsPS.B30
import Formal.Cells.CertRowsPS.B31
import Formal.Cells.CertRowsPS.B32
import Formal.Cells.CertRowsPS.B33
import Formal.Cells.CertRowsPS.B34
import Formal.Cells.CertRowsPS.B35
import Formal.Cells.CertRowsPS.B36
import Formal.Cells.CertRowsPS.B37
import Formal.Cells.CertRowsPS.B38
import Formal.Cells.CertRowsPS.B39
import Formal.Cells.CertRowsPS.B40
import Formal.Cells.CertRowsPS.B41
import Formal.Cells.CertRowsPS.B42
import Formal.Cells.CertRowsPS.B43
import Formal.Cells.CertRowsPS.B44
import Formal.Cells.CertRowsPS.B45
import Formal.Cells.CertRowsPS.B46
import Formal.Cells.CertRowsPS.B47
import Formal.Cells.CertRowsPS.B48
import Formal.Cells.CertRowsPS.B49
import Formal.Cells.CertRowsPS.B50
import Formal.Cells.CertRowsPS.B51
import Formal.Cells.CertRowsPS.B52
import Formal.Cells.CertRowsPS.B53
import Formal.Cells.CertRowsPS.B55
import Formal.Cells.CertRowsPS.B56
import Formal.Cells.CertRowsPS.B57
import Formal.Cells.CertRowsPS.B58
import Formal.Cells.CertRowsPS.B59
import Formal.Cells.CertRowsPS.B60
import Formal.Cells.CertRowsPS.B61
import Formal.Cells.CertRowsPS.B62
import Formal.Cells.CertRowsPS.B64
import Formal.Cells.CertRowsPS.B65
import Formal.Cells.CertRowsPS.B66
import Formal.Cells.CertRowsPS.B67
import Formal.Cells.CertRowsPS.B68
import Formal.Cells.CertRowsPS.B69
import Formal.Cells.CertRowsPS.B70
import Formal.Cells.CertRowsPS.B71
import Formal.Cells.CertRowsPS.B72
import Formal.Cells.CertRowsPS.B73
import Formal.Cells.CertRowsPS.B74
import Formal.Cells.CertRowsPS.B75
import Formal.Cells.CertRowsPS.B77
import Formal.Cells.CertRowsPS.B78
import Formal.Cells.CertRowsPS.B79
import Formal.Cells.CertRowsPS.B82
import Formal.Cells.CertRowsPS.B83
import Formal.Cells.CertRowsPS.B88

/-!
# Formal.Cells.CertRowsPS — hold certificates for 158 of the 185 RaceTablePS rows (GENERATED)

Each certificate: the storage node's own flip as the cause, its episode path's LUT steps as rows, the fewest static
premises; all checked by `CertPS.certOK` (kernel decide). With `CertPS.cert_sound`, in every behaviour each listed
node's acknowledge source keeps its value for the path's summed lower window ends after the node's flip, given the
premises. Skipped (no certificate from the dump used): 27 rows: SLICE_X16Y22.CLUT.O6, SLICE_X14Y19.BLUT.O6, SLICE_X16Y21.ALUT.O6, SLICE_X14Y17.ALUT.O6, SLICE_X14Y17.DLUT.O6, SLICE_X17Y17.ALUT.O6, SLICE_X16Y23.DLUT.O6, SLICE_X16Y22.ALUT.O6, SLICE_X4Y98.ALUT.O6, SLICE_X26Y51.ALUT.O6, SLICE_X6Y76.ALUT.O6, SLICE_X28Y48.ALUT.O6, SLICE_X28Y45.ALUT.O6, SLICE_X4Y28.ALUT.O6, SLICE_X8Y30.ALUT.O6, SLICE_X22Y18.DLUT.O6, SLICE_X22Y32.ALUT.O6, SLICE_X16Y86.ALUT.O6, SLICE_X4Y54.ALUT.O6, SLICE_X16Y78.ALUT.O6, SLICE_X4Y51.ALUT.O6, SLICE_X12Y80.ALUT.O6, SLICE_X12Y33.DLUT.O6, SLICE_X16Y25.BLUT.O6, SLICE_X10Y63.DLUT.O6, SLICE_X1Y84.DLUT.O6, SLICE_X16Y18.DLUT.O6.
Left out (one certificate spans more netlist chunks than one kernel check fits in memory here): SLICE_X16Y31.DLUT.O6, SLICE_X38Y21.CLUT.O6, SLICE_X39Y41.CLUT.O6, SLICE_X21Y45.BLUT.O6, SLICE_X0Y92.ALUT.O6, SLICE_X27Y52.BLUT.O6, SLICE_X14Y19.ALUT.O6, SLICE_X38Y51.BLUT.O6, SLICE_X38Y53.CLUT.O6, SLICE_X14Y83.CLUT.O6, SLICE_X17Y31.ALUT.O6, SLICE_X39Y41.DLUT.O6, SLICE_X4Y18.ALUT.O6, SLICE_X6Y47.DLUT.O6, SLICE_X36Y69.CLUT.O6, SLICE_X9Y97.CLUT.O6, SLICE_X12Y33.CLUT.O6, SLICE_X17Y48.DLUT.O6, SLICE_X35Y79.DLUT.O6, SLICE_X37Y63.DLUT.O6, SLICE_X18Y24.ALUT.O6, SLICE_X14Y18.ALUT.O6, SLICE_X14Y57.DLUT.O6.
-/

namespace Formal.Cells.CertRowsPS
open Formal.Cells.CertPS

set_option maxRecDepth 100000 in
def certs : List (Prem × List CRow) := certs00 ++ certs01 ++ certs02 ++ certs03 ++ certs04 ++ certs05 ++ certs06 ++ certs07 ++ certs08 ++ certs09 ++ certs10 ++ certs11 ++ certs12 ++ certs13 ++ certs14 ++ certs15 ++ certs16 ++ certs17 ++ certs18 ++ certs19 ++ certs20 ++ certs21 ++ certs22 ++ certs23 ++ certs24 ++ certs25 ++ certs26 ++ certs27 ++ certs28 ++ certs29 ++ certs30 ++ certs31 ++ certs32 ++ certs33 ++ certs34 ++ certs35 ++ certs36 ++ certs37 ++ certs38 ++ certs39 ++ certs40 ++ certs41 ++ certs42 ++ certs43 ++ certs44 ++ certs45 ++ certs46 ++ certs47 ++ certs48 ++ certs49 ++ certs50 ++ certs51 ++ certs52 ++ certs53 ++ certs55 ++ certs56 ++ certs57 ++ certs58 ++ certs59 ++ certs60 ++ certs61 ++ certs62 ++ certs64 ++ certs65 ++ certs66 ++ certs67 ++ certs68 ++ certs69 ++ certs70 ++ certs71 ++ certs72 ++ certs73 ++ certs74 ++ certs75 ++ certs77 ++ certs78 ++ certs79 ++ certs82 ++ certs83 ++ certs88

set_option maxRecDepth 100000 in
theorem certs_ok : certs.all (fun pc => certOK pc.1 pc.2) = true := by
  simp only [certs, List.all_append, certs00_ok, certs01_ok, certs02_ok, certs03_ok, certs04_ok, certs05_ok, certs06_ok, certs07_ok, certs08_ok, certs09_ok, certs10_ok, certs11_ok, certs12_ok, certs13_ok, certs14_ok, certs15_ok, certs16_ok, certs17_ok, certs18_ok, certs19_ok, certs20_ok, certs21_ok, certs22_ok, certs23_ok, certs24_ok, certs25_ok, certs26_ok, certs27_ok, certs28_ok, certs29_ok, certs30_ok, certs31_ok, certs32_ok, certs33_ok, certs34_ok, certs35_ok, certs36_ok, certs37_ok, certs38_ok, certs39_ok, certs40_ok, certs41_ok, certs42_ok, certs43_ok, certs44_ok, certs45_ok, certs46_ok, certs47_ok, certs48_ok, certs49_ok, certs50_ok, certs51_ok, certs52_ok, certs53_ok, certs55_ok, certs56_ok, certs57_ok, certs58_ok, certs59_ok, certs60_ok, certs61_ok, certs62_ok, certs64_ok, certs65_ok, certs66_ok, certs67_ok, certs68_ok, certs69_ok, certs70_ok, certs71_ok, certs72_ok, certs73_ok, certs74_ok, certs75_ok, certs77_ok, certs78_ok, certs79_ok, certs82_ok, certs83_ok, certs88_ok, Bool.and_self]

set_option maxRecDepth 100000 in
theorem certs_length : certs.length = 135 := by decide

end Formal.Cells.CertRowsPS

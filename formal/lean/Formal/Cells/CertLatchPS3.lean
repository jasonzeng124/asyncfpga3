import Formal.Cells.CertLatchPS3.B00
import Formal.Cells.CertLatchPS3.B01
import Formal.Cells.CertLatchPS3.B02
import Formal.Cells.CertLatchPS3.B03
import Formal.Cells.CertLatchPS3.B04
import Formal.Cells.CertLatchPS3.B05
import Formal.Cells.CertLatchPS3.B06
import Formal.Cells.CertLatchPS3.B07
import Formal.Cells.CertLatchPS3.B08
import Formal.Cells.CertLatchPS3.B09
import Formal.Cells.CertLatchPS3.B10
import Formal.Cells.CertLatchPS3.B11
import Formal.Cells.CertLatchPS3.B12
import Formal.Cells.CertLatchPS3.B13
import Formal.Cells.CertLatchPS3.B14
import Formal.Cells.CertLatchPS3.B15
import Formal.Cells.CertLatchPS3.B16
import Formal.Cells.CertLatchPS3.B17
import Formal.Cells.CertLatchPS3.B18
import Formal.Cells.CertLatchPS3.B19
import Formal.Cells.CertLatchPS3.B20
import Formal.Cells.CertLatchPS3.B21
import Formal.Cells.CertLatchPS3.B22
import Formal.Cells.CertLatchPS3.B23
import Formal.Cells.CertLatchPS3.B24
import Formal.Cells.CertLatchPS3.B25
import Formal.Cells.CertLatchPS3.B26
import Formal.Cells.CertLatchPS3.B27
import Formal.Cells.CertLatchPS3.B28
import Formal.Cells.CertLatchPS3.B29
import Formal.Cells.CertLatchPS3.B30
import Formal.Cells.CertLatchPS3.B31
import Formal.Cells.CertLatchPS3.B32
import Formal.Cells.CertLatchPS3.B33
import Formal.Cells.CertLatchPS3.B34
import Formal.Cells.CertLatchPS3.B35
import Formal.Cells.CertLatchPS3.B36
import Formal.Cells.CertLatchPS3.B37
import Formal.Cells.CertLatchPS3.B38
import Formal.Cells.CertLatchPS3.B39
import Formal.Cells.CertLatchPS3.B40
import Formal.Cells.CertLatchPS3.B41
import Formal.Cells.CertLatchPS3.B42
import Formal.Cells.CertLatchPS3.B43
import Formal.Cells.CertLatchPS3.B44
import Formal.Cells.CertLatchPS3.B45
import Formal.Cells.CertLatchPS3.B46
import Formal.Cells.CertLatchPS3.B47
import Formal.Cells.CertLatchPS3.B48
import Formal.Cells.CertLatchPS3.B49
import Formal.Cells.CertLatchPS3.B50
import Formal.Cells.CertLatchPS3.B51
import Formal.Cells.CertLatchPS3.B52
import Formal.Cells.CertLatchPS3.B53
import Formal.Cells.CertLatchPS3.B54
import Formal.Cells.CertLatchPS3.B55
import Formal.Cells.CertLatchPS3.B56
import Formal.Cells.CertLatchPS3.B57
import Formal.Cells.CertLatchPS3.B58
import Formal.Cells.CertLatchPS3.B59
import Formal.Cells.CertLatchPS3.B60
import Formal.Cells.CertLatchPS3.B61
import Formal.Cells.CertLatchPS3.B62
import Formal.Cells.CertLatchPS3.B63
import Formal.Cells.CertLatchPS3.B64
import Formal.Cells.CertLatchPS3.B65
import Formal.Cells.CertLatchPS3.B66
import Formal.Cells.CertLatchPS3.B67
import Formal.Cells.CertLatchPS3.B68
import Formal.Cells.CertLatchPS3.B69
import Formal.Cells.CertLatchPS3.B70
import Formal.Cells.CertLatchPS3.B71
import Formal.Cells.CertLatchPS3.B72
import Formal.Cells.CertLatchPS3.B73
import Formal.Cells.CertLatchPS3.B74
import Formal.Cells.CertLatchPS3.B75
import Formal.Cells.CertLatchPS3.B76
import Formal.Cells.CertLatchPS3.B77
import Formal.Cells.CertLatchPS3.B78
import Formal.Cells.CertLatchPS3.B79
import Formal.Cells.CertLatchPS3.B80
import Formal.Cells.CertLatchPS3.B81
import Formal.Cells.CertLatchPS3.B82
import Formal.Cells.CertLatchPS3.B83
import Formal.Cells.CertLatchPS3.B84
import Formal.Cells.CertLatchPS3.B85
import Formal.Cells.CertLatchPS3.B86
import Formal.Cells.CertLatchPS3.B87
import Formal.Cells.CertLatchPS3.B88
import Formal.Cells.CertLatchPS3.B89
import Formal.Cells.CertLatchPS3.B90
import Formal.Cells.CertLatchPS3.B91
import Formal.Cells.CertLatchPS3.B92
import Formal.Cells.CertLatchPS3.B93
import Formal.Cells.CertLatchPS3.B94
import Formal.Cells.CertLatchPS3.B95

/-!
# Formal.Cells.CertLatchPS3 — hold certificates for 344 of the 185 RaceTablePS rows (GENERATED)

Each certificate: the storage node's own flip as the cause, its episode path's LUT steps as rows, the fewest static
premises; all checked by `CertPS.certOK` (kernel decide). With `CertPS.cert_sound`, in every behaviour each listed
node's acknowledge source keeps its value for the path's summed lower window ends after the node's flip, given the
premises. Skipped (no certificate from the dump used): 0 rows: .
Left out (one certificate spans more netlist chunks than one kernel check fits in memory here): .
-/

namespace Formal.Cells.CertLatchPS3
open Formal.Cells.CertPS

set_option maxRecDepth 100000 in
def certs : List (Prem × List CRow) := certs00 ++ certs01 ++ certs02 ++ certs03 ++ certs04 ++ certs05 ++ certs06 ++ certs07 ++ certs08 ++ certs09 ++ certs10 ++ certs11 ++ certs12 ++ certs13 ++ certs14 ++ certs15 ++ certs16 ++ certs17 ++ certs18 ++ certs19 ++ certs20 ++ certs21 ++ certs22 ++ certs23 ++ certs24 ++ certs25 ++ certs26 ++ certs27 ++ certs28 ++ certs29 ++ certs30 ++ certs31 ++ certs32 ++ certs33 ++ certs34 ++ certs35 ++ certs36 ++ certs37 ++ certs38 ++ certs39 ++ certs40 ++ certs41 ++ certs42 ++ certs43 ++ certs44 ++ certs45 ++ certs46 ++ certs47 ++ certs48 ++ certs49 ++ certs50 ++ certs51 ++ certs52 ++ certs53 ++ certs54 ++ certs55 ++ certs56 ++ certs57 ++ certs58 ++ certs59 ++ certs60 ++ certs61 ++ certs62 ++ certs63 ++ certs64 ++ certs65 ++ certs66 ++ certs67 ++ certs68 ++ certs69 ++ certs70 ++ certs71 ++ certs72 ++ certs73 ++ certs74 ++ certs75 ++ certs76 ++ certs77 ++ certs78 ++ certs79 ++ certs80 ++ certs81 ++ certs82 ++ certs83 ++ certs84 ++ certs85 ++ certs86 ++ certs87 ++ certs88 ++ certs89 ++ certs90 ++ certs91 ++ certs92 ++ certs93 ++ certs94 ++ certs95

set_option maxRecDepth 100000 in
theorem certs_ok : certs.all (fun pc => certOK pc.1 pc.2) = true := by
  simp only [certs, List.all_append, certs00_ok, certs01_ok, certs02_ok, certs03_ok, certs04_ok, certs05_ok, certs06_ok, certs07_ok, certs08_ok, certs09_ok, certs10_ok, certs11_ok, certs12_ok, certs13_ok, certs14_ok, certs15_ok, certs16_ok, certs17_ok, certs18_ok, certs19_ok, certs20_ok, certs21_ok, certs22_ok, certs23_ok, certs24_ok, certs25_ok, certs26_ok, certs27_ok, certs28_ok, certs29_ok, certs30_ok, certs31_ok, certs32_ok, certs33_ok, certs34_ok, certs35_ok, certs36_ok, certs37_ok, certs38_ok, certs39_ok, certs40_ok, certs41_ok, certs42_ok, certs43_ok, certs44_ok, certs45_ok, certs46_ok, certs47_ok, certs48_ok, certs49_ok, certs50_ok, certs51_ok, certs52_ok, certs53_ok, certs54_ok, certs55_ok, certs56_ok, certs57_ok, certs58_ok, certs59_ok, certs60_ok, certs61_ok, certs62_ok, certs63_ok, certs64_ok, certs65_ok, certs66_ok, certs67_ok, certs68_ok, certs69_ok, certs70_ok, certs71_ok, certs72_ok, certs73_ok, certs74_ok, certs75_ok, certs76_ok, certs77_ok, certs78_ok, certs79_ok, certs80_ok, certs81_ok, certs82_ok, certs83_ok, certs84_ok, certs85_ok, certs86_ok, certs87_ok, certs88_ok, certs89_ok, certs90_ok, certs91_ok, certs92_ok, certs93_ok, certs94_ok, certs95_ok, Bool.and_self]

set_option maxRecDepth 100000 in
theorem certs_length : certs.length = 344 := by decide

end Formal.Cells.CertLatchPS3

import Formal.Net.CViewPS.RIslChk00
import Formal.Net.CViewPS.RIslChk01
import Formal.Net.CViewPS.RIslChk02
import Formal.Net.CViewPS.RIslChk03
import Formal.Net.CViewPS.RIslChk04
import Formal.Net.CViewPS.RIslChk05
import Formal.Net.CViewPS.RIslChk06
import Formal.Net.CViewPS.RIslChk07
import Formal.Net.CViewPS.RIslChk08
import Formal.Net.CViewPS.RIslChk09
import Formal.Net.CViewPS.RIslChk10
import Formal.Net.CViewPS.RIslChk11
import Formal.Net.CViewPS.RIslChk12
import Formal.Net.CViewPS.RIslChk13
import Formal.Net.CViewPS.RIslChk14
import Formal.Net.CViewPS.RIslChk15
import Formal.Net.CViewPS.RIslChk16
import Formal.Net.CViewPS.RIslChk17
import Formal.Net.CViewPS.RIslChk18
import Formal.Net.CViewPS.RIslChk19
import Formal.Net.CViewPS.RIslChk20
import Formal.Net.CViewPS.RIslChk21
import Formal.Net.CViewPS.RIslChk22
import Formal.Net.CViewPS.RIslChk23
import Formal.Net.CViewPS.RIslChk24
import Formal.Net.CViewPS.RIslChk25
import Formal.Net.CViewPS.RIslChk26
import Formal.Net.CViewPS.RIslChk27
import Formal.Net.CViewPS.RIslChk28
import Formal.Net.CViewPS.RIslChk29
import Formal.Net.CViewPS.RIslChk30
import Formal.Net.CViewPS.RIslChk31
import Formal.Net.CViewPS.RIslChk32
import Formal.Net.CViewPS.RIslChk33
import Formal.Net.CViewPS.RIslChk34
import Formal.Net.CViewPS.RIslChk35
import Formal.Net.CViewPS.RIslChk36
import Formal.Net.CViewPS.RIslChk37
import Formal.Net.CViewPS.RIslChk38
import Formal.Net.CViewPS.RIslChk39
import Formal.Net.CViewPS.RIslChk40
import Formal.Net.CViewPS.RIslChk41
import Formal.Net.CViewPS.RIslChk42
import Formal.Net.CViewPS.RIslChk43
import Formal.Net.CViewPS.RIslChk44
import Formal.Net.CViewPS.RIslChk45
import Formal.Net.CViewPS.RIslChk46
import Formal.Net.CViewPS.RIslChk47
import Formal.Net.CViewPS.RIslChk48
import Formal.Net.CViewPS.RIslChk49
import Formal.Net.CViewPS.RIslChk50
import Formal.Net.CViewPS.RIslChk51
import Formal.Net.CViewPS.RIslChk52
import Formal.Net.CViewPS.RIslChk53
import Formal.Net.CViewPS.RIslChk54
import Formal.Net.CViewPS.RIslChk55
import Formal.Net.CViewPS.RIslChk56
import Formal.Net.CViewPS.RIslChk57
import Formal.Net.CViewPS.RIslChk58
import Formal.Net.CViewPS.RIslChk59
import Formal.Net.CViewPS.RIslChk60
import Formal.Net.CViewPS.RIslChk61

/-! Shard C: every entry of the reset island passes `rEntryOK` (the 62 block checks, assembled). -/

namespace Formal.Net.CViewPS

theorem rIsl_ok : rIsl.all rEntryOK = true := by
  simp only [rIsl, RTree.all,
    rb0_ok, rb1_ok, rb2_ok, rb3_ok, rb4_ok, rb5_ok, rb6_ok, rb7_ok, rb8_ok, rb9_ok, rb10_ok, rb11_ok, rb12_ok, rb13_ok, rb14_ok, rb15_ok, rb16_ok, rb17_ok, rb18_ok, rb19_ok, rb20_ok, rb21_ok, rb22_ok, rb23_ok, rb24_ok, rb25_ok, rb26_ok, rb27_ok, rb28_ok, rb29_ok, rb30_ok, rb31_ok, rb32_ok, rb33_ok, rb34_ok, rb35_ok, rb36_ok, rb37_ok, rb38_ok, rb39_ok, rb40_ok, rb41_ok, rb42_ok, rb43_ok, rb44_ok, rb45_ok, rb46_ok, rb47_ok, rb48_ok, rb49_ok, rb50_ok, rb51_ok, rb52_ok, rb53_ok, rb54_ok, rb55_ok, rb56_ok, rb57_ok, rb58_ok, rb59_ok, rb60_ok, rb61_ok, Bool.and_self]

end Formal.Net.CViewPS

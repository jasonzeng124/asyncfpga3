module noremon;
  // ucontrol_merge10.uarb1.g1: request net n66150, DQ 563, window [tau - 563, tau + 277) (hi Dq 761 + 2 - lo Dr 486)
  realtime lrise_c_002281_1 = -1.0e9; realtime lfall_c_002281_1 = -1.0e9; realtime until_c_002281_1 = -1.0e9;
  always @(negedge tb_run.dut.n66150) lfall_c_002281_1 = $realtime;
  always @(negedge tb_run.dut.n66257) begin until_c_002281_1 = $realtime + (277); $display("NORE_FLIP %0t ucontrol_merge10.uarb1.g1", $realtime); if ((tb_run.dut.n66150 !== 1'b0 && lrise_c_002281_1 < $realtime + (277) && $realtime + (277) > $realtime - 563) || (tb_run.dut.n66150 === 1'b0 && (277) > -563 && lfall_c_002281_1 > $realtime - 563 && lrise_c_002281_1 < $realtime + (277))) $display("NORE_VIOL %0t ucontrol_merge10.uarb1.g1 pre", $realtime); end
  always @(posedge tb_run.dut.n66150) begin lrise_c_002281_1 = $realtime; if ($realtime < until_c_002281_1) $display("NORE_VIOL %0t ucontrol_merge10.uarb1.g1 post %0t", $realtime, until_c_002281_1 - $realtime); end
  // ucontrol_merge10.uarb1.g2: request net n66180, DQ 836, window [tau - 836, tau + -333) (hi Dq 735 + 2 - lo Dr 1070)
  realtime lrise_c_002281_2 = -1.0e9; realtime lfall_c_002281_2 = -1.0e9; realtime until_c_002281_2 = -1.0e9;
  always @(negedge tb_run.dut.n66180) lfall_c_002281_2 = $realtime;
  always @(posedge tb_run.dut.n66257) begin until_c_002281_2 = $realtime + (-333); $display("NORE_FLIP %0t ucontrol_merge10.uarb1.g2", $realtime); if ((tb_run.dut.n66180 !== 1'b0 && lrise_c_002281_2 < $realtime + (-333) && $realtime + (-333) > $realtime - 836) || (tb_run.dut.n66180 === 1'b0 && (-333) > -836 && lfall_c_002281_2 > $realtime - 836 && lrise_c_002281_2 < $realtime + (-333))) $display("NORE_VIOL %0t ucontrol_merge10.uarb1.g2 pre", $realtime); end
  always @(posedge tb_run.dut.n66180) begin lrise_c_002281_2 = $realtime; if ($realtime < until_c_002281_2) $display("NORE_VIOL %0t ucontrol_merge10.uarb1.g2 post %0t", $realtime, until_c_002281_2 - $realtime); end
  // ucontrol_merge11.uarb1.g1: request net n65165, DQ 742, window [tau - 742, tau + -520) (hi Dq 426 + 2 - lo Dr 948)
  realtime lrise_c_002295_1 = -1.0e9; realtime lfall_c_002295_1 = -1.0e9; realtime until_c_002295_1 = -1.0e9;
  always @(negedge tb_run.dut.n65165) lfall_c_002295_1 = $realtime;
  always @(negedge tb_run.dut.n66384) begin until_c_002295_1 = $realtime + (-520); $display("NORE_FLIP %0t ucontrol_merge11.uarb1.g1", $realtime); if ((tb_run.dut.n65165 !== 1'b0 && lrise_c_002295_1 < $realtime + (-520) && $realtime + (-520) > $realtime - 742) || (tb_run.dut.n65165 === 1'b0 && (-520) > -742 && lfall_c_002295_1 > $realtime - 742 && lrise_c_002295_1 < $realtime + (-520))) $display("NORE_VIOL %0t ucontrol_merge11.uarb1.g1 pre", $realtime); end
  always @(posedge tb_run.dut.n65165) begin lrise_c_002295_1 = $realtime; if ($realtime < until_c_002295_1) $display("NORE_VIOL %0t ucontrol_merge11.uarb1.g1 post %0t", $realtime, until_c_002295_1 - $realtime); end
  // ucontrol_merge11.uarb1.g2: request net n65416, DQ 558, window [tau - 558, tau + -232) (hi Dq 398 + 2 - lo Dr 632)
  realtime lrise_c_002295_2 = -1.0e9; realtime lfall_c_002295_2 = -1.0e9; realtime until_c_002295_2 = -1.0e9;
  always @(negedge tb_run.dut.n65416) lfall_c_002295_2 = $realtime;
  always @(posedge tb_run.dut.n66384) begin until_c_002295_2 = $realtime + (-232); $display("NORE_FLIP %0t ucontrol_merge11.uarb1.g2", $realtime); if ((tb_run.dut.n65416 !== 1'b0 && lrise_c_002295_2 < $realtime + (-232) && $realtime + (-232) > $realtime - 558) || (tb_run.dut.n65416 === 1'b0 && (-232) > -558 && lfall_c_002295_2 > $realtime - 558 && lrise_c_002295_2 < $realtime + (-232))) $display("NORE_VIOL %0t ucontrol_merge11.uarb1.g2 pre", $realtime); end
  always @(posedge tb_run.dut.n65416) begin lrise_c_002295_2 = $realtime; if ($realtime < until_c_002295_2) $display("NORE_VIOL %0t ucontrol_merge11.uarb1.g2 post %0t", $realtime, until_c_002295_2 - $realtime); end
  // ucontrol_merge12.uarb1.g1: request net n63164, DQ 559, window [tau - 559, tau + 19) (hi Dq 806 + 2 - lo Dr 789)
  realtime lrise_c_002314_1 = -1.0e9; realtime lfall_c_002314_1 = -1.0e9; realtime until_c_002314_1 = -1.0e9;
  always @(negedge tb_run.dut.n63164) lfall_c_002314_1 = $realtime;
  always @(negedge tb_run.dut.n66548) begin until_c_002314_1 = $realtime + (19); $display("NORE_FLIP %0t ucontrol_merge12.uarb1.g1", $realtime); if ((tb_run.dut.n63164 !== 1'b0 && lrise_c_002314_1 < $realtime + (19) && $realtime + (19) > $realtime - 559) || (tb_run.dut.n63164 === 1'b0 && (19) > -559 && lfall_c_002314_1 > $realtime - 559 && lrise_c_002314_1 < $realtime + (19))) $display("NORE_VIOL %0t ucontrol_merge12.uarb1.g1 pre", $realtime); end
  always @(posedge tb_run.dut.n63164) begin lrise_c_002314_1 = $realtime; if ($realtime < until_c_002314_1) $display("NORE_VIOL %0t ucontrol_merge12.uarb1.g1 post %0t", $realtime, until_c_002314_1 - $realtime); end
  // ucontrol_merge12.uarb1.g2: request net n63343, DQ 572, window [tau - 572, tau + 7) (hi Dq 778 + 2 - lo Dr 773)
  realtime lrise_c_002314_2 = -1.0e9; realtime lfall_c_002314_2 = -1.0e9; realtime until_c_002314_2 = -1.0e9;
  always @(negedge tb_run.dut.n63343) lfall_c_002314_2 = $realtime;
  always @(posedge tb_run.dut.n66548) begin until_c_002314_2 = $realtime + (7); $display("NORE_FLIP %0t ucontrol_merge12.uarb1.g2", $realtime); if ((tb_run.dut.n63343 !== 1'b0 && lrise_c_002314_2 < $realtime + (7) && $realtime + (7) > $realtime - 572) || (tb_run.dut.n63343 === 1'b0 && (7) > -572 && lfall_c_002314_2 > $realtime - 572 && lrise_c_002314_2 < $realtime + (7))) $display("NORE_VIOL %0t ucontrol_merge12.uarb1.g2 pre", $realtime); end
  always @(posedge tb_run.dut.n63343) begin lrise_c_002314_2 = $realtime; if ($realtime < until_c_002314_2) $display("NORE_VIOL %0t ucontrol_merge12.uarb1.g2 post %0t", $realtime, until_c_002314_2 - $realtime); end
  // ucontrol_merge12.uarb2.g1: request net n66560, DQ 419, window [tau - 419, tau + 124) (hi Dq 822 + 2 - lo Dr 700)
  realtime lrise_c_002320_1 = -1.0e9; realtime lfall_c_002320_1 = -1.0e9; realtime until_c_002320_1 = -1.0e9;
  always @(negedge tb_run.dut.n66560) lfall_c_002320_1 = $realtime;
  always @(negedge tb_run.dut.n66579) begin until_c_002320_1 = $realtime + (124); $display("NORE_FLIP %0t ucontrol_merge12.uarb2.g1", $realtime); if ((tb_run.dut.n66560 !== 1'b0 && lrise_c_002320_1 < $realtime + (124) && $realtime + (124) > $realtime - 419) || (tb_run.dut.n66560 === 1'b0 && (124) > -419 && lfall_c_002320_1 > $realtime - 419 && lrise_c_002320_1 < $realtime + (124))) $display("NORE_VIOL %0t ucontrol_merge12.uarb2.g1 pre", $realtime); end
  always @(posedge tb_run.dut.n66560) begin lrise_c_002320_1 = $realtime; if ($realtime < until_c_002320_1) $display("NORE_VIOL %0t ucontrol_merge12.uarb2.g1 post %0t", $realtime, until_c_002320_1 - $realtime); end
  // ucontrol_merge12.uarb2.g2: request net n66338, DQ 755, window [tau - 755, tau + -28) (hi Dq 796 + 2 - lo Dr 826)
  realtime lrise_c_002320_2 = -1.0e9; realtime lfall_c_002320_2 = -1.0e9; realtime until_c_002320_2 = -1.0e9;
  always @(negedge tb_run.dut.n66338) lfall_c_002320_2 = $realtime;
  always @(posedge tb_run.dut.n66579) begin until_c_002320_2 = $realtime + (-28); $display("NORE_FLIP %0t ucontrol_merge12.uarb2.g2", $realtime); if ((tb_run.dut.n66338 !== 1'b0 && lrise_c_002320_2 < $realtime + (-28) && $realtime + (-28) > $realtime - 755) || (tb_run.dut.n66338 === 1'b0 && (-28) > -755 && lfall_c_002320_2 > $realtime - 755 && lrise_c_002320_2 < $realtime + (-28))) $display("NORE_VIOL %0t ucontrol_merge12.uarb2.g2 pre", $realtime); end
  always @(posedge tb_run.dut.n66338) begin lrise_c_002320_2 = $realtime; if ($realtime < until_c_002320_2) $display("NORE_VIOL %0t ucontrol_merge12.uarb2.g2 post %0t", $realtime, until_c_002320_2 - $realtime); end
  // ucontrol_merge2.uarb1.g1: request net n63697, DQ 710, window [tau - 710, tau + -399) (hi Dq 441 + 2 - lo Dr 842)
  realtime lrise_c_002335_1 = -1.0e9; realtime lfall_c_002335_1 = -1.0e9; realtime until_c_002335_1 = -1.0e9;
  always @(negedge tb_run.dut.n63697) lfall_c_002335_1 = $realtime;
  always @(negedge tb_run.dut.n66712) begin until_c_002335_1 = $realtime + (-399); $display("NORE_FLIP %0t ucontrol_merge2.uarb1.g1", $realtime); if ((tb_run.dut.n63697 !== 1'b0 && lrise_c_002335_1 < $realtime + (-399) && $realtime + (-399) > $realtime - 710) || (tb_run.dut.n63697 === 1'b0 && (-399) > -710 && lfall_c_002335_1 > $realtime - 710 && lrise_c_002335_1 < $realtime + (-399))) $display("NORE_VIOL %0t ucontrol_merge2.uarb1.g1 pre", $realtime); end
  always @(posedge tb_run.dut.n63697) begin lrise_c_002335_1 = $realtime; if ($realtime < until_c_002335_1) $display("NORE_VIOL %0t ucontrol_merge2.uarb1.g1 post %0t", $realtime, until_c_002335_1 - $realtime); end
  // ucontrol_merge2.uarb1.g2: request net n66648, DQ 562, window [tau - 562, tau + -543) (hi Dq 413 + 2 - lo Dr 958)
  realtime lrise_c_002335_2 = -1.0e9; realtime lfall_c_002335_2 = -1.0e9; realtime until_c_002335_2 = -1.0e9;
  always @(negedge tb_run.dut.n66648) lfall_c_002335_2 = $realtime;
  always @(posedge tb_run.dut.n66712) begin until_c_002335_2 = $realtime + (-543); $display("NORE_FLIP %0t ucontrol_merge2.uarb1.g2", $realtime); if ((tb_run.dut.n66648 !== 1'b0 && lrise_c_002335_2 < $realtime + (-543) && $realtime + (-543) > $realtime - 562) || (tb_run.dut.n66648 === 1'b0 && (-543) > -562 && lfall_c_002335_2 > $realtime - 562 && lrise_c_002335_2 < $realtime + (-543))) $display("NORE_VIOL %0t ucontrol_merge2.uarb1.g2 pre", $realtime); end
  always @(posedge tb_run.dut.n66648) begin lrise_c_002335_2 = $realtime; if ($realtime < until_c_002335_2) $display("NORE_VIOL %0t ucontrol_merge2.uarb1.g2 post %0t", $realtime, until_c_002335_2 - $realtime); end
  // ucontrol_merge3.uarb1.g1: request net n63694, DQ 981, window [tau - 981, tau + -510) (hi Dq 579 + 2 - lo Dr 1091)
  realtime lrise_c_002350_1 = -1.0e9; realtime lfall_c_002350_1 = -1.0e9; realtime until_c_002350_1 = -1.0e9;
  always @(negedge tb_run.dut.n63694) lfall_c_002350_1 = $realtime;
  always @(negedge tb_run.dut.n66847) begin until_c_002350_1 = $realtime + (-510); $display("NORE_FLIP %0t ucontrol_merge3.uarb1.g1", $realtime); if ((tb_run.dut.n63694 !== 1'b0 && lrise_c_002350_1 < $realtime + (-510) && $realtime + (-510) > $realtime - 981) || (tb_run.dut.n63694 === 1'b0 && (-510) > -981 && lfall_c_002350_1 > $realtime - 981 && lrise_c_002350_1 < $realtime + (-510))) $display("NORE_VIOL %0t ucontrol_merge3.uarb1.g1 pre", $realtime); end
  always @(posedge tb_run.dut.n63694) begin lrise_c_002350_1 = $realtime; if ($realtime < until_c_002350_1) $display("NORE_VIOL %0t ucontrol_merge3.uarb1.g1 post %0t", $realtime, until_c_002350_1 - $realtime); end
  // ucontrol_merge3.uarb1.g2: request net n63966, DQ 419, window [tau - 419, tau + -406) (hi Dq 551 + 2 - lo Dr 959)
  realtime lrise_c_002350_2 = -1.0e9; realtime lfall_c_002350_2 = -1.0e9; realtime until_c_002350_2 = -1.0e9;
  always @(negedge tb_run.dut.n63966) lfall_c_002350_2 = $realtime;
  always @(posedge tb_run.dut.n66847) begin until_c_002350_2 = $realtime + (-406); $display("NORE_FLIP %0t ucontrol_merge3.uarb1.g2", $realtime); if ((tb_run.dut.n63966 !== 1'b0 && lrise_c_002350_2 < $realtime + (-406) && $realtime + (-406) > $realtime - 419) || (tb_run.dut.n63966 === 1'b0 && (-406) > -419 && lfall_c_002350_2 > $realtime - 419 && lrise_c_002350_2 < $realtime + (-406))) $display("NORE_VIOL %0t ucontrol_merge3.uarb1.g2 pre", $realtime); end
  always @(posedge tb_run.dut.n63966) begin lrise_c_002350_2 = $realtime; if ($realtime < until_c_002350_2) $display("NORE_VIOL %0t ucontrol_merge3.uarb1.g2 post %0t", $realtime, until_c_002350_2 - $realtime); end
  // ucontrol_merge4.uarb1.g1: request net n66803, DQ 1866, window [tau - 1866, tau + -989) (hi Dq 999 + 2 - lo Dr 1990)
  realtime lrise_c_002364_1 = -1.0e9; realtime lfall_c_002364_1 = -1.0e9; realtime until_c_002364_1 = -1.0e9;
  always @(negedge tb_run.dut.n66803) lfall_c_002364_1 = $realtime;
  always @(negedge tb_run.dut.n66981) begin until_c_002364_1 = $realtime + (-989); $display("NORE_FLIP %0t ucontrol_merge4.uarb1.g1", $realtime); if ((tb_run.dut.n66803 !== 1'b0 && lrise_c_002364_1 < $realtime + (-989) && $realtime + (-989) > $realtime - 1866) || (tb_run.dut.n66803 === 1'b0 && (-989) > -1866 && lfall_c_002364_1 > $realtime - 1866 && lrise_c_002364_1 < $realtime + (-989))) $display("NORE_VIOL %0t ucontrol_merge4.uarb1.g1 pre", $realtime); end
  always @(posedge tb_run.dut.n66803) begin lrise_c_002364_1 = $realtime; if ($realtime < until_c_002364_1) $display("NORE_VIOL %0t ucontrol_merge4.uarb1.g1 post %0t", $realtime, until_c_002364_1 - $realtime); end
  // ucontrol_merge4.uarb1.g2: request net n66915, DQ 707, window [tau - 707, tau + 296) (hi Dq 966 + 2 - lo Dr 672)
  realtime lrise_c_002364_2 = -1.0e9; realtime lfall_c_002364_2 = -1.0e9; realtime until_c_002364_2 = -1.0e9;
  always @(negedge tb_run.dut.n66915) lfall_c_002364_2 = $realtime;
  always @(posedge tb_run.dut.n66981) begin until_c_002364_2 = $realtime + (296); $display("NORE_FLIP %0t ucontrol_merge4.uarb1.g2", $realtime); if ((tb_run.dut.n66915 !== 1'b0 && lrise_c_002364_2 < $realtime + (296) && $realtime + (296) > $realtime - 707) || (tb_run.dut.n66915 === 1'b0 && (296) > -707 && lfall_c_002364_2 > $realtime - 707 && lrise_c_002364_2 < $realtime + (296))) $display("NORE_VIOL %0t ucontrol_merge4.uarb1.g2 pre", $realtime); end
  always @(posedge tb_run.dut.n66915) begin lrise_c_002364_2 = $realtime; if ($realtime < until_c_002364_2) $display("NORE_VIOL %0t ucontrol_merge4.uarb1.g2 post %0t", $realtime, until_c_002364_2 - $realtime); end
  // ucontrol_merge6.uarb1.g1: request net n64396, DQ 2809, window [tau - 2809, tau + -2446) (hi Dq 450 + 2 - lo Dr 2898)
  realtime lrise_c_002382_1 = -1.0e9; realtime lfall_c_002382_1 = -1.0e9; realtime until_c_002382_1 = -1.0e9;
  always @(negedge tb_run.dut.n64396) lfall_c_002382_1 = $realtime;
  always @(negedge tb_run.dut.n67125) begin until_c_002382_1 = $realtime + (-2446); $display("NORE_FLIP %0t ucontrol_merge6.uarb1.g1", $realtime); if ((tb_run.dut.n64396 !== 1'b0 && lrise_c_002382_1 < $realtime + (-2446) && $realtime + (-2446) > $realtime - 2809) || (tb_run.dut.n64396 === 1'b0 && (-2446) > -2809 && lfall_c_002382_1 > $realtime - 2809 && lrise_c_002382_1 < $realtime + (-2446))) $display("NORE_VIOL %0t ucontrol_merge6.uarb1.g1 pre", $realtime); end
  always @(posedge tb_run.dut.n64396) begin lrise_c_002382_1 = $realtime; if ($realtime < until_c_002382_1) $display("NORE_VIOL %0t ucontrol_merge6.uarb1.g1 post %0t", $realtime, until_c_002382_1 - $realtime); end
  // ucontrol_merge6.uarb1.g2: request net n67061, DQ 708, window [tau - 708, tau + -398) (hi Dq 422 + 2 - lo Dr 822)
  realtime lrise_c_002382_2 = -1.0e9; realtime lfall_c_002382_2 = -1.0e9; realtime until_c_002382_2 = -1.0e9;
  always @(negedge tb_run.dut.n67061) lfall_c_002382_2 = $realtime;
  always @(posedge tb_run.dut.n67125) begin until_c_002382_2 = $realtime + (-398); $display("NORE_FLIP %0t ucontrol_merge6.uarb1.g2", $realtime); if ((tb_run.dut.n67061 !== 1'b0 && lrise_c_002382_2 < $realtime + (-398) && $realtime + (-398) > $realtime - 708) || (tb_run.dut.n67061 === 1'b0 && (-398) > -708 && lfall_c_002382_2 > $realtime - 708 && lrise_c_002382_2 < $realtime + (-398))) $display("NORE_VIOL %0t ucontrol_merge6.uarb1.g2 pre", $realtime); end
  always @(posedge tb_run.dut.n67061) begin lrise_c_002382_2 = $realtime; if ($realtime < until_c_002382_2) $display("NORE_VIOL %0t ucontrol_merge6.uarb1.g2 post %0t", $realtime, until_c_002382_2 - $realtime); end
  // ucontrol_merge9.uarb1.g1: request net n65162, DQ 762, window [tau - 762, tau + -332) (hi Dq 872 + 2 - lo Dr 1206)
  realtime lrise_c_002401_1 = -1.0e9; realtime lfall_c_002401_1 = -1.0e9; realtime until_c_002401_1 = -1.0e9;
  always @(negedge tb_run.dut.n65162) lfall_c_002401_1 = $realtime;
  always @(negedge tb_run.dut.n67273) begin until_c_002401_1 = $realtime + (-332); $display("NORE_FLIP %0t ucontrol_merge9.uarb1.g1", $realtime); if ((tb_run.dut.n65162 !== 1'b0 && lrise_c_002401_1 < $realtime + (-332) && $realtime + (-332) > $realtime - 762) || (tb_run.dut.n65162 === 1'b0 && (-332) > -762 && lfall_c_002401_1 > $realtime - 762 && lrise_c_002401_1 < $realtime + (-332))) $display("NORE_VIOL %0t ucontrol_merge9.uarb1.g1 pre", $realtime); end
  always @(posedge tb_run.dut.n65162) begin lrise_c_002401_1 = $realtime; if ($realtime < until_c_002401_1) $display("NORE_VIOL %0t ucontrol_merge9.uarb1.g1 post %0t", $realtime, until_c_002401_1 - $realtime); end
  // ucontrol_merge9.uarb1.g2: request net n65413, DQ 632, window [tau - 632, tau + 25) (hi Dq 846 + 2 - lo Dr 823)
  realtime lrise_c_002401_2 = -1.0e9; realtime lfall_c_002401_2 = -1.0e9; realtime until_c_002401_2 = -1.0e9;
  always @(negedge tb_run.dut.n65413) lfall_c_002401_2 = $realtime;
  always @(posedge tb_run.dut.n67273) begin until_c_002401_2 = $realtime + (25); $display("NORE_FLIP %0t ucontrol_merge9.uarb1.g2", $realtime); if ((tb_run.dut.n65413 !== 1'b0 && lrise_c_002401_2 < $realtime + (25) && $realtime + (25) > $realtime - 632) || (tb_run.dut.n65413 === 1'b0 && (25) > -632 && lfall_c_002401_2 > $realtime - 632 && lrise_c_002401_2 < $realtime + (25))) $display("NORE_VIOL %0t ucontrol_merge9.uarb1.g2 pre", $realtime); end
  always @(posedge tb_run.dut.n65413) begin lrise_c_002401_2 = $realtime; if ($realtime < until_c_002401_2) $display("NORE_VIOL %0t ucontrol_merge9.uarb1.g2 post %0t", $realtime, until_c_002401_2 - $realtime); end
endmodule

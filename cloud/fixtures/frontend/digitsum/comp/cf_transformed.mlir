module {
  func.func @digitsum(%arg0: i32 {handshake.arg_name = "x"}, %arg1: i32 {handshake.arg_name = "base"}) -> i32 {
    %c2_i32 = arith.constant {handshake.name = "constant0"} 2 : i32
    %c10_i32 = arith.constant {handshake.name = "constant1"} 10 : i32
    %c0_i32 = arith.constant {handshake.name = "constant2"} 0 : i32
    %0 = arith.cmpi ult, %arg1, %c2_i32 {handshake.name = "cmpi0"} : i32
    %1 = arith.select %0, %c10_i32, %arg1 {handshake.name = "select0"} : i32
    %2 = arith.cmpi eq, %arg0, %c0_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %2, ^bb2(%c0_i32 : i32), ^bb1(%c0_i32, %arg0 : i32, i32) {handshake.name = "cond_br0"}
  ^bb1(%3: i32, %4: i32):  // 2 preds: ^bb0, ^bb1
    %c0_i32_0 = arith.constant {handshake.name = "constant3"} 0 : i32
    %5 = arith.divui %4, %1 {handshake.name = "divui0"} : i32
    %6 = arith.muli %5, %1 {handshake.name = "muli0"} : i32
    %7 = arith.subi %4, %6 {handshake.name = "subi0"} : i32
    %8 = arith.addi %3, %7 {handshake.name = "addi0"} : i32
    %9 = arith.cmpi eq, %5, %c0_i32_0 {handshake.name = "cmpi2"} : i32
    cf.cond_br %9, ^bb2(%8 : i32), ^bb1(%8, %5 : i32, i32) {handshake.name = "cond_br1"}
  ^bb2(%10: i32):  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"} %10 : i32
  }
}


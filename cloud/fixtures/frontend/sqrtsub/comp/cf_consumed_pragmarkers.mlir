module {
  func.func @sqrtsub(%arg0: i32 {handshake.arg_name = "n"}) -> i32 {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %0 = arith.cmpi slt, %arg0, %c1_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb2(%c0_i32 : i32), ^bb1(%arg0, %c0_i32, %c1_i32 : i32, i32, i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32, %3: i32):  // 2 preds: ^bb0, ^bb1
    %c2_i32 = arith.constant {handshake.name = "constant3"} 2 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant4"} 1 : i32
    %4 = arith.subi %1, %3 {handshake.name = "subi0"} : i32
    %5 = arith.addi %3, %c2_i32 {handshake.name = "addi0"} : i32
    %6 = arith.addi %2, %c1_i32_0 {handshake.name = "addi1"} : i32
    %7 = arith.cmpi slt, %4, %5 {handshake.name = "cmpi1"} : i32
    cf.cond_br %7, ^bb2(%6 : i32), ^bb1(%4, %6, %5 : i32, i32, i32) {handshake.name = "cond_br1"}
  ^bb2(%8: i32):  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"} %8 : i32
  }
}


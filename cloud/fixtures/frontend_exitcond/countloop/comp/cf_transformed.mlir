module {
  func.func @countloop(%arg0: i32 {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "n"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c0_i32 : i32, i32), ^bb2(%c0_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant2"} 1 : i32
    %3 = arith.addi %2, %1 {handshake.name = "addi0"} : i32
    %4 = arith.xori %3, %arg0 {handshake.name = "xori0"} : i32
    %5 = arith.addi %1, %c1_i32 {handshake.name = "addi1"} : i32
    %6 = arith.cmpi ne, %5, %arg1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %6, ^bb1(%5, %4 : i32, i32), ^bb2(%4 : i32) {handshake.name = "cond_br1"}
  ^bb2(%7: i32):  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"} %7 : i32
  }
}


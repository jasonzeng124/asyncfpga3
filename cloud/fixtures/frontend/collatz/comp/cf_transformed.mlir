module {
  func.func @collatz(%arg0: i32 {handshake.arg_name = "n"}) -> i32 {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %0 = arith.cmpi eq, %arg0, %c1_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb2(%c0_i32 : i32), ^bb1(%arg0, %c0_i32 : i32, i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %c0_i32_0 = arith.constant {handshake.name = "constant3"} 0 : i32
    %c1_i32_1 = arith.constant {handshake.name = "constant4"} 1 : i32
    %3 = arith.andi %1, %c1_i32_1 {handshake.name = "andi0"} : i32
    %4 = arith.cmpi eq, %3, %c0_i32_0 {handshake.name = "cmpi1"} : i32
    %5 = arith.shrsi %1, %c1_i32_1 {handshake.name = "shrsi0"} : i32
    %6 = arith.shli %1, %c1_i32_1 {handshake.name = "shli0"} : i32
    %7 = arith.addi %1, %6 {handshake.name = "addi2"} : i32
    %8 = arith.addi %7, %c1_i32_1 {handshake.name = "addi0"} : i32
    %9 = arith.select %4, %5, %8 {handshake.name = "select0"} : i32
    %10 = arith.addi %2, %c1_i32_1 {handshake.name = "addi1"} : i32
    %11 = arith.cmpi eq, %9, %c1_i32_1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %11, ^bb2(%10 : i32), ^bb1(%9, %10 : i32, i32) {handshake.name = "cond_br1"}
  ^bb2(%12: i32):  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"} %12 : i32
  }
}


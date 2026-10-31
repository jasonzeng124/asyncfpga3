module {
  func.func @collatz64(%arg0: i64 {handshake.arg_name = "n"}) -> i32 {
    %c1_i64 = arith.constant {handshake.name = "constant0"} 1 : i64
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %0 = arith.cmpi eq, %arg0, %c1_i64 {handshake.name = "cmpi0"} : i64
    cf.cond_br %0, ^bb2(%c0_i32 : i32), ^bb1(%arg0, %c0_i32 : i64, i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i64, %2: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant5"} 1 : i32
    %c0_i64 = arith.constant {handshake.name = "constant6"} 0 : i64
    %c1_i64_0 = arith.constant {handshake.name = "constant7"} 1 : i64
    %3 = arith.andi %1, %c1_i64_0 {handshake.name = "andi0"} : i64
    %4 = arith.cmpi eq, %3, %c0_i64 {handshake.name = "cmpi1"} : i64
    %5 = arith.shrsi %1, %c1_i64_0 {handshake.name = "shrsi0"} : i64
    %6 = arith.shli %1, %c1_i64_0 {handshake.name = "shli0"} : i64
    %7 = arith.addi %1, %6 {handshake.name = "addi2"} : i64
    %8 = arith.addi %7, %c1_i64_0 {handshake.name = "addi0"} : i64
    %9 = arith.select %4, %5, %8 {handshake.name = "select0"} : i64
    %10 = arith.addi %2, %c1_i32 {handshake.name = "addi1"} : i32
    %11 = arith.cmpi eq, %9, %c1_i64_0 {handshake.name = "cmpi2"} : i64
    cf.cond_br %11, ^bb2(%10 : i32), ^bb1(%9, %10 : i64, i32) {handshake.name = "cond_br1"}
  ^bb2(%12: i32):  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"} %12 : i32
  }
}


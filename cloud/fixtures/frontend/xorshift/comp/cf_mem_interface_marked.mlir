module {
  func.func @xorshift(%arg0: i32 {handshake.arg_name = "seed"}, %arg1: i32 {handshake.arg_name = "rounds"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32, %arg0 : i32, i32), ^bb2(%arg0 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant5"} 1 : i32
    %c5_i32 = arith.constant {handshake.name = "constant6"} 5 : i32
    %c17_i32 = arith.constant {handshake.name = "constant7"} 17 : i32
    %c13_i32 = arith.constant {handshake.name = "constant8"} 13 : i32
    %3 = arith.shli %2, %c13_i32 {handshake.name = "shli0"} : i32
    %4 = arith.xori %2, %3 {handshake.name = "xori0"} : i32
    %5 = arith.shrui %4, %c17_i32 {handshake.name = "shrui0"} : i32
    %6 = arith.xori %4, %5 {handshake.name = "xori1"} : i32
    %7 = arith.shli %6, %c5_i32 {handshake.name = "shli1"} : i32
    %8 = arith.xori %6, %7 {handshake.name = "xori2"} : i32
    %9 = arith.addi %1, %c1_i32 {handshake.name = "addi0"} : i32
    %10 = arith.cmpi slt, %9, %arg1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %10, ^bb1(%9, %8 : i32, i32), ^bb2(%8 : i32) {handshake.name = "cond_br1"}
  ^bb2(%11: i32):  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"} %11 : i32
  }
}


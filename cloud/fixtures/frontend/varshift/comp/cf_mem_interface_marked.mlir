module {
  func.func @varshift(%arg0: i32 {handshake.arg_name = "x"}, %arg1: i32 {handshake.arg_name = "n"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %c1540483477_i32 = arith.constant {handshake.name = "constant1"} 1540483477 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c1540483477_i32 : i32, i32), ^bb2(%c1540483477_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant6"} 1 : i32
    %c31_i32 = arith.constant {handshake.name = "constant7"} 31 : i32
    %c7_i32 = arith.constant {handshake.name = "constant8"} 7 : i32
    %c27_i32 = arith.constant {handshake.name = "constant9"} 27 : i32
    %3 = arith.shrui %2, %c27_i32 {handshake.name = "shrui0"} : i32
    %4 = arith.andi %3, %c7_i32 {handshake.name = "andi0"} : i32
    %5 = arith.shli %2, %4 {handshake.name = "shli0"} : i32
    %6 = arith.shrui %arg0, %3 {handshake.name = "shrui1"} : i32
    %7 = arith.xori %5, %6 {handshake.name = "xori0"} : i32
    %8 = arith.xori %3, %c31_i32 {handshake.name = "xori1"} : i32
    %9 = arith.shrsi %2, %8 {handshake.name = "shrsi0"} : i32
    %10 = arith.xori %7, %9 {handshake.name = "xori2"} : i32
    %11 = arith.xori %10, %1 {handshake.name = "xori3"} : i32
    %12 = arith.addi %1, %c1_i32 {handshake.name = "addi0"} : i32
    %13 = arith.cmpi slt, %12, %arg1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %13, ^bb1(%12, %11 : i32, i32), ^bb2(%11 : i32) {handshake.name = "cond_br1"}
  ^bb2(%14: i32):  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"} %14 : i32
  }
}


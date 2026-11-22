module {
  func.func @brhash(%arg0: i32 {handshake.arg_name = "x"}, %arg1: i32 {handshake.arg_name = "n"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32, %arg0 : i32, i32), ^bb5(%arg0 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb4
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant11"} 0 : i32
    %3 = arith.andi %2, %c1_i32 {handshake.name = "andi0"} : i32
    %4 = arith.cmpi eq, %3, %c0_i32_0 {handshake.name = "cmpi1"} : i32
    cf.cond_br %4, ^bb3, ^bb2 {handshake.name = "cond_br1"}
  ^bb2:  // pred: ^bb1
    %c13_i32 = arith.constant {handshake.name = "constant12"} 13 : i32
    %c-306674912_i32 = arith.constant {handshake.name = "constant13"} -306674912 : i32
    %c1_i32_1 = arith.constant {handshake.name = "constant14"} 1 : i32
    %c4_i32 = arith.constant {handshake.name = "constant15"} 4 : i32
    %5 = arith.shrui %2, %c1_i32_1 {handshake.name = "shrui0"} : i32
    %6 = arith.xori %5, %c-306674912_i32 {handshake.name = "xori0"} : i32
    %7 = arith.shli %6, %c4_i32 {handshake.name = "shli3"} : i32
    %8 = arith.addi %6, %7 {handshake.name = "addi3"} : i32
    %9 = arith.addi %8, %1 {handshake.name = "addi0"} : i32
    %10 = arith.shrui %9, %c13_i32 {handshake.name = "shrui1"} : i32
    %11 = arith.xori %9, %10 {handshake.name = "xori1"} : i32
    cf.br ^bb4(%11 : i32) {handshake.name = "br0"}
  ^bb3:  // pred: ^bb1
    %c625341585_i32 = arith.constant {handshake.name = "constant16"} 625341585 : i32
    %c5_i32 = arith.constant {handshake.name = "constant17"} 5 : i32
    %c2_i32 = arith.constant {handshake.name = "constant18"} 2 : i32
    %c9_i32 = arith.constant {handshake.name = "constant19"} 9 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant20"} 1 : i32
    %12 = arith.shli %2, %c9_i32 {handshake.name = "shli0"} : i32
    %13 = arith.xori %2, %12 {handshake.name = "xori2"} : i32
    %14 = arith.shrui %13, %c2_i32 {handshake.name = "shrui2"} : i32
    %15 = arith.shli %1, %c1_i32_2 {handshake.name = "shli1"} : i32
    %16 = arith.addi %14, %15 {handshake.name = "addi1"} : i32
    %17 = arith.shli %16, %c5_i32 {handshake.name = "shli2"} : i32
    %18 = arith.xori %16, %17 {handshake.name = "xori3"} : i32
    %19 = arith.xori %18, %c625341585_i32 {handshake.name = "xori4"} : i32
    cf.br ^bb4(%19 : i32) {handshake.name = "br1"}
  ^bb4(%20: i32):  // 2 preds: ^bb2, ^bb3
    %c1_i32_3 = arith.constant {handshake.name = "constant21"} 1 : i32
    %21 = arith.addi %1, %c1_i32_3 {handshake.name = "addi2"} : i32
    %22 = arith.cmpi ne, %21, %arg1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %22, ^bb1(%21, %20 : i32, i32), ^bb5(%20 : i32) {handshake.name = "cond_br2"}
  ^bb5(%23: i32):  // 2 preds: ^bb0, ^bb4
    return {handshake.name = "return0"} %23 : i32
  }
}


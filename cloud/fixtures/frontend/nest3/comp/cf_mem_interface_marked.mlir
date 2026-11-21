module {
  func.func @nest3(%arg0: i32 {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "b"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %c74565_i32 = arith.constant {handshake.name = "constant1"} 74565 : i32
    %0 = arith.cmpi sgt, %arg0, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c74565_i32, %c0_i32 : i32, i32), ^bb6(%c74565_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant7"} 0 : i32
    %3 = arith.cmpi sgt, %arg1, %c0_i32_0 {handshake.name = "cmpi1"} : i32
    cf.cond_br %3, ^bb2(%c0_i32_0, %1 : i32, i32), ^bb5(%1 : i32) {handshake.name = "cond_br1"}
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb1, ^bb4
    %c3_i32 = arith.constant {handshake.name = "constant8"} 3 : i32
    %c0_i32_1 = arith.constant {handshake.name = "constant9"} 0 : i32
    %6 = arith.xori %2, %4 {handshake.name = "xori0"} : i32
    %7 = arith.andi %6, %c3_i32 {handshake.name = "andi0"} : i32
    %8 = arith.cmpi ugt, %7, %c0_i32_1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %8, ^bb3(%c0_i32_1, %5 : i32, i32), ^bb4(%5 : i32) {handshake.name = "cond_br2"}
  ^bb3(%9: i32, %10: i32):  // 2 preds: ^bb2, ^bb3
    %c1_i32 = arith.constant {handshake.name = "constant10"} 1 : i32
    %c2_i32 = arith.constant {handshake.name = "constant11"} 2 : i32
    %c4_i32 = arith.constant {handshake.name = "constant12"} 4 : i32
    %c5_i32 = arith.constant {handshake.name = "constant13"} 5 : i32
    %11 = arith.shrui %10, %c5_i32 {handshake.name = "shrui0"} : i32
    %12 = arith.xori %10, %11 {handshake.name = "xori1"} : i32
    %13 = arith.shli %2, %c4_i32 {handshake.name = "shli0"} : i32
    %14 = arith.shli %4, %c2_i32 {handshake.name = "shli1"} : i32
    %15 = arith.xori %13, %14 {handshake.name = "xori2"} : i32
    %16 = arith.xori %15, %9 {handshake.name = "xori3"} : i32
    %17 = arith.addi %12, %16 {handshake.name = "addi0"} : i32
    %18 = arith.addi %17, %c1_i32 {handshake.name = "addi1"} : i32
    %19 = arith.addi %9, %c1_i32 {handshake.name = "addi2"} : i32
    %20 = arith.cmpi ult, %19, %7 {handshake.name = "cmpi3"} : i32
    cf.cond_br %20, ^bb3(%19, %18 : i32, i32), ^bb4(%18 : i32) {handshake.name = "cond_br3"}
  ^bb4(%21: i32):  // 2 preds: ^bb2, ^bb3
    %c1_i32_2 = arith.constant {handshake.name = "constant14"} 1 : i32
    %22 = arith.addi %4, %c1_i32_2 {handshake.name = "addi3"} : i32
    %23 = arith.cmpi slt, %22, %arg1 {handshake.name = "cmpi4"} : i32
    cf.cond_br %23, ^bb2(%22, %21 : i32, i32), ^bb5(%21 : i32) {handshake.name = "cond_br4"}
  ^bb5(%24: i32):  // 2 preds: ^bb1, ^bb4
    %c1_i32_3 = arith.constant {handshake.name = "constant15"} 1 : i32
    %25 = arith.addi %2, %c1_i32_3 {handshake.name = "addi4"} : i32
    %26 = arith.cmpi slt, %25, %arg0 {handshake.name = "cmpi5"} : i32
    cf.cond_br %26, ^bb1(%24, %25 : i32, i32), ^bb6(%24 : i32) {handshake.name = "cond_br5"}
  ^bb6(%27: i32):  // 2 preds: ^bb0, ^bb5
    return {handshake.name = "return0"} %27 : i32
  }
}


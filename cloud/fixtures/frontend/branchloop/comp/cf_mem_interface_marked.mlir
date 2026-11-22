module {
  func.func @branchloop(%arg0: i32 {handshake.arg_name = "n"}) -> i32 {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %0 = arith.cmpi sgt, %arg0, %c1_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%arg0, %c0_i32 : i32, i32), ^bb7(%c0_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb6
    %c0_i32_0 = arith.constant {handshake.name = "constant3"} 0 : i32
    %c1_i32_1 = arith.constant {handshake.name = "constant4"} 1 : i32
    %3 = arith.andi %1, %c1_i32_1 {handshake.name = "andi0"} : i32
    %4 = arith.cmpi eq, %3, %c0_i32_0 {handshake.name = "cmpi1"} : i32
    cf.cond_br %4, ^bb5, ^bb2 {handshake.name = "cond_br1"}
  ^bb2:  // pred: ^bb1
    %c3_i32 = arith.constant {handshake.name = "constant5"} 3 : i32
    %5 = arith.andi %1, %c3_i32 {handshake.name = "andi1"} : i32
    %6 = arith.cmpi eq, %5, %c3_i32 {handshake.name = "cmpi2"} : i32
    cf.cond_br %6, ^bb3(%1, %2 : i32, i32), ^bb4(%2, %1 : i32, i32) {handshake.name = "cond_br2"}
  ^bb3(%7: i32, %8: i32):  // 2 preds: ^bb2, ^bb3
    %c3_i32_2 = arith.constant {handshake.name = "constant6"} 3 : i32
    %c1_i32_3 = arith.constant {handshake.name = "constant7"} 1 : i32
    %9 = arith.shrsi %7, %c1_i32_3 {handshake.name = "shrsi0"} : i32
    %10 = arith.addi %8, %c1_i32_3 {handshake.name = "addi0"} : i32
    %11 = arith.andi %9, %c3_i32_2 {handshake.name = "andi2"} : i32
    %12 = arith.cmpi eq, %11, %c3_i32_2 {handshake.name = "cmpi3"} : i32
    cf.cond_br %12, ^bb3(%9, %10 : i32, i32), ^bb4(%10, %9 : i32, i32) {handshake.name = "cond_br3"}
  ^bb4(%13: i32, %14: i32):  // 2 preds: ^bb2, ^bb3
    %c1_i32_4 = arith.constant {handshake.name = "constant8"} 1 : i32
    %15 = arith.addi %14, %c1_i32_4 {handshake.name = "addi1"} : i32
    cf.br ^bb6(%13, %15 : i32, i32) {handshake.name = "br0"}
  ^bb5:  // pred: ^bb1
    %c1_i32_5 = arith.constant {handshake.name = "constant9"} 1 : i32
    %16 = arith.shrsi %1, %c1_i32_5 {handshake.name = "shrsi1"} : i32
    cf.br ^bb6(%2, %16 : i32, i32) {handshake.name = "br1"}
  ^bb6(%17: i32, %18: i32):  // 2 preds: ^bb4, ^bb5
    %c1_i32_6 = arith.constant {handshake.name = "constant10"} 1 : i32
    %19 = arith.addi %17, %c1_i32_6 {handshake.name = "addi2"} : i32
    %20 = arith.cmpi sgt, %18, %c1_i32_6 {handshake.name = "cmpi4"} : i32
    cf.cond_br %20, ^bb1(%18, %19 : i32, i32), ^bb7(%19 : i32) {handshake.name = "cond_br4"}
  ^bb7(%21: i32):  // 2 preds: ^bb0, ^bb6
    return {handshake.name = "return0"} %21 : i32
  }
}


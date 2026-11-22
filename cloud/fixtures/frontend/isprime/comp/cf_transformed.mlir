module {
  func.func @isprime(%arg0: i32 {handshake.arg_name = "n"}) -> i32 {
    %c2_i32 = arith.constant {handshake.name = "constant0"} 2 : i32
    %c0_i32 = arith.constant {handshake.name = "constant3"} 0 : i32
    %0 = arith.cmpi slt, %arg0, %c2_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb8(%c0_i32 : i32), ^bb1 {handshake.name = "cond_br0"}
  ^bb1:  // pred: ^bb0
    %c1_i32 = arith.constant {handshake.name = "constant4"} 1 : i32
    %c4_i32 = arith.constant {handshake.name = "constant5"} 4 : i32
    %c2_i32_0 = arith.constant {handshake.name = "constant6"} 2 : i32
    %1 = arith.cmpi slt, %arg0, %c4_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %1, ^bb8(%c1_i32 : i32), ^bb3(%c2_i32_0 : i32) {handshake.name = "cond_br1"}
  ^bb2(%2: i32):  // pred: ^bb7
    %c1_i32_1 = arith.constant {handshake.name = "constant7"} 1 : i32
    %3 = arith.muli %2, %2 {handshake.name = "muli0"} : i32
    %4 = arith.cmpi sgt, %3, %arg0 {handshake.name = "cmpi2"} : i32
    cf.cond_br %4, ^bb8(%c1_i32_1 : i32), ^bb3(%2 : i32) {handshake.name = "cond_br2"}
  ^bb3(%5: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32_2 = arith.constant {handshake.name = "constant8"} 1 : i32
    %6 = arith.shrsi %arg0, %c1_i32_2 {handshake.name = "shrsi0"} : i32
    cf.br ^bb4(%5 : i32) {handshake.name = "br0"}
  ^bb4(%7: i32):  // 2 preds: ^bb3, ^bb4
    %c1_i32_3 = arith.constant {handshake.name = "constant9"} 1 : i32
    %8 = arith.cmpi sgt, %7, %6 {handshake.name = "cmpi3"} : i32
    %9 = arith.shli %7, %c1_i32_3 {handshake.name = "shli0"} : i32
    cf.cond_br %8, ^bb5(%7 : i32), ^bb4(%9 : i32) {handshake.name = "cond_br3"}
  ^bb5(%10: i32):  // pred: ^bb4
    %11 = arith.cmpi slt, %10, %5 {handshake.name = "cmpi4"} : i32
    cf.cond_br %11, ^bb7(%arg0 : i32), ^bb6(%10, %arg0 : i32, i32) {handshake.name = "cond_br4"}
  ^bb6(%12: i32, %13: i32):  // 2 preds: ^bb5, ^bb6
    %c1_i32_4 = arith.constant {handshake.name = "constant10"} 1 : i32
    %14 = arith.cmpi slt, %13, %12 {handshake.name = "cmpi5"} : i32
    %15 = arith.subi %13, %12 {handshake.name = "subi0"} : i32
    %16 = arith.select %14, %13, %15 {handshake.name = "select0"} : i32
    %17 = arith.shrsi %12, %c1_i32_4 {handshake.name = "shrsi1"} : i32
    %18 = arith.cmpi slt, %17, %5 {handshake.name = "cmpi6"} : i32
    cf.cond_br %18, ^bb7(%16 : i32), ^bb6(%17, %16 : i32, i32) {handshake.name = "cond_br5"}
  ^bb7(%19: i32):  // 2 preds: ^bb5, ^bb6
    %c0_i32_5 = arith.constant {handshake.name = "constant11"} 0 : i32
    %c1_i32_6 = arith.constant {handshake.name = "constant12"} 1 : i32
    %20 = arith.cmpi eq, %19, %c0_i32_5 {handshake.name = "cmpi7"} : i32
    %21 = arith.addi %5, %c1_i32_6 {handshake.name = "addi0"} : i32
    cf.cond_br %20, ^bb8(%c0_i32_5 : i32), ^bb2(%21 : i32) {handshake.name = "cond_br6"}
  ^bb8(%22: i32):  // 4 preds: ^bb0, ^bb1, ^bb2, ^bb7
    return {handshake.name = "return0"} %22 : i32
  }
}


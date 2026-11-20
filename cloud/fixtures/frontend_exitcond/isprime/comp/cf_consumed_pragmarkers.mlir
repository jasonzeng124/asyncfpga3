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
  ^bb2:  // pred: ^bb7
    %c1_i32_1 = arith.constant {handshake.name = "constant7"} 1 : i32
    %2 = arith.muli %20, %20 {handshake.name = "muli0"} : i32
    %3 = arith.cmpi sgt, %2, %arg0 {handshake.name = "cmpi2"} : i32
    cf.cond_br %3, ^bb8(%c1_i32_1 : i32), ^bb3(%20 : i32) {handshake.name = "cond_br2"}
  ^bb3(%4: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32_2 = arith.constant {handshake.name = "constant8"} 1 : i32
    %5 = arith.shrsi %arg0, %c1_i32_2 {handshake.name = "shrsi0"} : i32
    cf.br ^bb4(%4 : i32) {handshake.name = "br0"}
  ^bb4(%6: i32):  // 2 preds: ^bb3, ^bb4
    %c1_i32_3 = arith.constant {handshake.name = "constant9"} 1 : i32
    %7 = arith.cmpi sgt, %6, %5 {handshake.name = "cmpi3"} : i32
    %8 = arith.shli %6, %c1_i32_3 {handshake.name = "shli0"} : i32
    cf.cond_br %7, ^bb5(%6 : i32), ^bb4(%8 : i32) {handshake.name = "cond_br3"}
  ^bb5(%9: i32):  // pred: ^bb4
    %10 = arith.cmpi slt, %9, %4 {handshake.name = "cmpi4"} : i32
    cf.cond_br %10, ^bb7(%arg0 : i32), ^bb6(%9, %arg0 : i32, i32) {handshake.name = "cond_br4"}
  ^bb6(%11: i32, %12: i32):  // 2 preds: ^bb5, ^bb6
    %c1_i32_4 = arith.constant {handshake.name = "constant10"} 1 : i32
    %13 = arith.cmpi slt, %12, %11 {handshake.name = "cmpi5"} : i32
    %14 = arith.subi %12, %11 {handshake.name = "subi0"} : i32
    %15 = arith.select %13, %12, %14 {handshake.name = "select0"} : i32
    %16 = arith.shrsi %11, %c1_i32_4 {handshake.name = "shrsi1"} : i32
    %17 = arith.cmpi slt, %16, %4 {handshake.name = "cmpi6"} : i32
    cf.cond_br %17, ^bb7(%15 : i32), ^bb6(%16, %15 : i32, i32) {handshake.name = "cond_br5"}
  ^bb7(%18: i32):  // 2 preds: ^bb5, ^bb6
    %c0_i32_5 = arith.constant {handshake.name = "constant11"} 0 : i32
    %c1_i32_6 = arith.constant {handshake.name = "constant12"} 1 : i32
    %19 = arith.cmpi eq, %18, %c0_i32_5 {handshake.name = "cmpi7"} : i32
    %20 = arith.addi %4, %c1_i32_6 {handshake.name = "addi0"} : i32
    cf.cond_br %19, ^bb8(%c0_i32_5 : i32), ^bb2 {handshake.name = "cond_br6"}
  ^bb8(%21: i32):  // 4 preds: ^bb0, ^bb1, ^bb2, ^bb7
    return {handshake.name = "return0"} %21 : i32
  }
}


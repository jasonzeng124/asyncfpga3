module {
  func.func @nested(%arg0: i32 {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "b"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %c1_i32 = arith.constant {handshake.name = "constant1"} 1 : i32
    %0 = arith.cmpi sgt, %arg0, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c0_i32, %c1_i32 : i32, i32), ^bb4(%c1_i32 : i32) {handshake.name = "cond_br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant3"} 0 : i32
    %3 = arith.cmpi sgt, %arg1, %c0_i32_0 {handshake.name = "cmpi1"} : i32
    cf.cond_br %3, ^bb2(%c0_i32_0, %2 : i32, i32), ^bb3(%2 : i32) {handshake.name = "cond_br1"}
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb1, ^bb2
    %c3_i32 = arith.constant {handshake.name = "constant4"} 3 : i32
    %c1_i32_1 = arith.constant {handshake.name = "constant5"} 1 : i32
    %6 = arith.shli %5, %c3_i32 {handshake.name = "shli0"} : i32
    %7 = arith.xori %5, %6 {handshake.name = "xori0"} : i32
    %8 = arith.addi %7, %1 {handshake.name = "addi0"} : i32
    %9 = arith.addi %8, %4 {handshake.name = "addi1"} : i32
    %10 = arith.addi %4, %c1_i32_1 {handshake.name = "addi2"} : i32
    %11 = arith.cmpi ne, %10, %arg1 {handshake.name = "cmpi2"} : i32
    cf.cond_br %11, ^bb2(%10, %9 : i32, i32), ^bb3(%9 : i32) {handshake.name = "cond_br2"}
  ^bb3(%12: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32_2 = arith.constant {handshake.name = "constant6"} 1 : i32
    %13 = arith.addi %1, %c1_i32_2 {handshake.name = "addi3"} : i32
    %14 = arith.cmpi ne, %13, %arg0 {handshake.name = "cmpi3"} : i32
    cf.cond_br %14, ^bb1(%13, %12 : i32, i32), ^bb4(%12 : i32) {handshake.name = "cond_br3"}
  ^bb4(%15: i32):  // 2 preds: ^bb0, ^bb3
    return {handshake.name = "return0"} %15 : i32
  }
}


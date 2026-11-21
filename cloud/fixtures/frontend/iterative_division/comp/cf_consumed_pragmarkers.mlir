module {
  func.func @iterative_division(%arg0: i32 {handshake.arg_name = "dividend"}, %arg1: i32 {handshake.arg_name = "divisor"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %c-1_i32 = arith.constant {handshake.name = "constant1"} -1 : i32
    %0 = arith.cmpi eq, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb4(%c-1_i32 : i32), ^bb1 {handshake.name = "cond_br0"}
  ^bb1:  // pred: ^bb0
    %c-1_i32_0 = arith.constant {handshake.name = "constant3"} -1 : i32
    %c0_i32_1 = arith.constant {handshake.name = "constant4"} 0 : i32
    %1 = arith.cmpi sgt, %arg0, %c-1_i32_0 {handshake.name = "cmpi1"} : i32
    %2 = arith.subi %c0_i32_1, %arg0 {handshake.name = "subi0"} : i32
    %3 = arith.select %1, %arg0, %2 {handshake.name = "select0"} : i32
    %4 = arith.cmpi sgt, %arg1, %c-1_i32_0 {handshake.name = "cmpi2"} : i32
    %5 = arith.subi %c0_i32_1, %arg1 {handshake.name = "subi1"} : i32
    %6 = arith.select %4, %arg1, %5 {handshake.name = "select1"} : i32
    %7 = arith.cmpi slt, %3, %6 {handshake.name = "cmpi3"} : i32
    cf.cond_br %7, ^bb3(%c0_i32_1 : i32), ^bb2(%3, %c0_i32_1 : i32, i32) {handshake.name = "cond_br1"}
  ^bb2(%8: i32, %9: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32 = arith.constant {handshake.name = "constant5"} 1 : i32
    %10 = arith.subi %8, %6 {handshake.name = "subi2"} : i32
    %11 = arith.addi %9, %c1_i32 {handshake.name = "addi0"} : i32
    %12 = arith.cmpi slt, %10, %6 {handshake.name = "cmpi4"} : i32
    cf.cond_br %12, ^bb3(%11 : i32), ^bb2(%10, %11 : i32, i32) {handshake.name = "cond_br2"}
  ^bb3(%13: i32):  // 2 preds: ^bb1, ^bb2
    %c0_i32_2 = arith.constant {handshake.name = "constant6"} 0 : i32
    %14 = arith.xori %arg0, %arg1 {handshake.name = "xori0"} : i32
    %15 = arith.cmpi slt, %14, %c0_i32_2 {handshake.name = "cmpi5"} : i32
    %16 = arith.subi %c0_i32_2, %13 {handshake.name = "subi3"} : i32
    %17 = arith.select %15, %16, %13 {handshake.name = "select2"} : i32
    cf.br ^bb4(%17 : i32) {handshake.name = "br0"}
  ^bb4(%18: i32):  // 2 preds: ^bb0, ^bb3
    return {handshake.name = "return0"} %18 : i32
  }
}


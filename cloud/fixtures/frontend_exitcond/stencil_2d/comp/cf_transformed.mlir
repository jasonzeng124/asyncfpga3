module {
  func.func @stencil_2d(%arg0: memref<900xi32> {handshake.arg_name = "orig"}, %arg1: memref<10xi32> {handshake.arg_name = "filter"}, %arg2: memref<900xi32> {handshake.arg_name = "sol"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant7"} 0 : i32
    cf.br ^bb2(%c0_i32_0, %c0_i32_0 : i32, i32) {handshake.name = "br1"}
  ^bb2(%1: i32, %2: i32):  // 2 preds: ^bb1, ^bb4
    %c1_i32 = arith.constant {handshake.name = "constant8"} 1 : i32
    %c3_i32 = arith.constant {handshake.name = "constant9"} 3 : i32
    %c0_i32_1 = arith.constant {handshake.name = "constant10"} 0 : i32
    %c4_i32 = arith.constant {handshake.name = "constant11"} 4 : i32
    %c2_i32 = arith.constant {handshake.name = "constant12"} 2 : i32
    %3 = arith.shli %1, %c1_i32 {handshake.name = "shli0"} : i32
    %4 = arith.addi %1, %3 {handshake.name = "addi7"} : i32
    %5 = arith.shli %1, %c1_i32 {handshake.name = "shli1"} : i32
    %6 = arith.shli %1, %c2_i32 {handshake.name = "shli2"} : i32
    %7 = arith.addi %5, %6 {handshake.name = "addi8"} : i32
    %8 = arith.shli %1, %c3_i32 {handshake.name = "shli3"} : i32
    %9 = arith.shli %1, %c4_i32 {handshake.name = "shli4"} : i32
    %10 = arith.addi %8, %9 {handshake.name = "addi9"} : i32
    %11 = arith.addi %7, %10 {handshake.name = "addi10"} : i32
    %12 = arith.addi %11, %0 {handshake.name = "addi0"} : i32
    cf.br ^bb3(%c0_i32_1, %2 : i32, i32) {handshake.name = "br2"}
  ^bb3(%13: i32, %14: i32):  // 2 preds: ^bb2, ^bb3
    %c1_i32_2 = arith.constant {handshake.name = "constant13"} 1 : i32
    %c3_i32_3 = arith.constant {handshake.name = "constant14"} 3 : i32
    %15 = arith.addi %4, %13 {handshake.name = "addi1"} : i32
    %16 = arith.extui %15 {handshake.name = "extui0"} : i32 to i64
    %17 = arith.index_cast %16 {handshake.name = "index_cast0"} : i64 to index
    %18 = memref.load %arg1[%17] {handshake.name = "load0"} : memref<10xi32>
    %19 = arith.addi %12, %13 {handshake.name = "addi2"} : i32
    %20 = arith.extui %19 {handshake.name = "extui1"} : i32 to i64
    %21 = arith.index_cast %20 {handshake.name = "index_cast1"} : i64 to index
    %22 = memref.load %arg0[%21] {handshake.name = "load1"} : memref<900xi32>
    %23 = arith.muli %18, %22 {handshake.name = "muli2"} : i32
    %24 = arith.addi %14, %23 {handshake.name = "addi3"} : i32
    %25 = arith.addi %13, %c1_i32_2 {handshake.name = "addi4"} : i32
    %26 = arith.cmpi ne, %25, %c3_i32_3 {handshake.name = "cmpi0"} : i32
    cf.cond_br %26, ^bb3(%25, %24 : i32, i32), ^bb4(%24 : i32) {handshake.name = "cond_br0"}
  ^bb4(%27: i32):  // pred: ^bb3
    %c1_i32_4 = arith.constant {handshake.name = "constant15"} 1 : i32
    %c3_i32_5 = arith.constant {handshake.name = "constant16"} 3 : i32
    %28 = arith.addi %1, %c1_i32_4 {handshake.name = "addi5"} : i32
    %29 = arith.cmpi ne, %28, %c3_i32_5 {handshake.name = "cmpi1"} : i32
    cf.cond_br %29, ^bb2(%28, %27 : i32, i32), ^bb5(%27 : i32) {handshake.name = "cond_br1"}
  ^bb5(%30: i32):  // pred: ^bb4
    %c28_i32 = arith.constant {handshake.name = "constant17"} 28 : i32
    %c1_i32_6 = arith.constant {handshake.name = "constant18"} 1 : i32
    %31 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %32 = arith.index_cast %31 {handshake.name = "index_cast2"} : i64 to index
    memref.store %30, %arg2[%32] {handshake.name = "store2"} : memref<900xi32>
    %33 = arith.addi %0, %c1_i32_6 {handshake.name = "addi6"} : i32
    %34 = arith.cmpi ne, %33, %c28_i32 {handshake.name = "cmpi2"} : i32
    cf.cond_br %34, ^bb1(%33 : i32), ^bb6(%30 : i32) {handshake.name = "cond_br2"}
  ^bb6(%35: i32):  // pred: ^bb5
    return {handshake.name = "return0"} %35 : i32
  }
}


module {
  func.func @test_flatten_array(%arg0: memref<512xi32> {handshake.arg_name = "input"}, %arg1: memref<512xi32> {handshake.arg_name = "output"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %c0_i32_0 = arith.constant {handshake.name = "constant9"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb4
    %c7_i32 = arith.constant {handshake.name = "constant10"} 7 : i32
    %c0_i32_1 = arith.constant {handshake.name = "constant11"} 0 : i32
    %4 = arith.subi %c7_i32, %3 {handshake.name = "subi0"} : i32
    %5 = arith.extsi %4 {handshake.name = "extsi0"} : i32 to i64
    %6 = arith.extui %3 {handshake.name = "extui2"} : i32 to i64
    cf.br ^bb3(%c0_i32_1 : i32) {handshake.name = "br2"}
  ^bb3(%7: i32):  // 2 preds: ^bb2, ^bb3
    %c16_i32 = arith.constant {handshake.name = "constant12"} 16 : i32
    %c1_i32 = arith.constant {handshake.name = "constant13"} 1 : i32
    %c15_i32 = arith.constant {handshake.name = "constant14"} 15 : i32
    %c7_i64 = arith.constant {handshake.name = "constant15"} 7 : i64
    %c4_i64 = arith.constant {handshake.name = "constant16"} 4 : i64
    %8 = arith.subi %c15_i32, %7 {handshake.name = "subi1"} : i32
    %9 = arith.extsi %8 {handshake.name = "extsi1"} : i32 to i64
    %10 = arith.shli %1, %c7_i64 {handshake.name = "shli0"} : i64
    %11 = arith.shli %5, %c4_i64 {handshake.name = "shli1"} : i64
    %12 = arith.addi %11, %9 {handshake.name = "addi0"} : i64
    %13 = arith.addi %10, %12 {handshake.name = "addi1"} : i64
    %14 = arith.index_cast %13 {handshake.name = "index_cast0"} : i64 to index
    %15 = memref.load %arg0[%14] {handshake.name = "load0"} : memref<512xi32>
    %16 = arith.extui %7 {handshake.name = "extui3"} : i32 to i64
    %17 = arith.shli %2, %c7_i64 {handshake.name = "shli2"} : i64
    %18 = arith.shli %6, %c4_i64 {handshake.name = "shli3"} : i64
    %19 = arith.addi %18, %16 {handshake.name = "addi2"} : i64
    %20 = arith.addi %17, %19 {handshake.name = "addi3"} : i64
    %21 = arith.index_cast %20 {handshake.name = "index_cast1"} : i64 to index
    memref.store %15, %arg1[%21] {handshake.name = "store1"} : memref<512xi32>
    %22 = arith.addi %7, %c1_i32 {handshake.name = "addi4"} : i32
    %23 = arith.cmpi ult, %22, %c16_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %23, ^bb3(%22 : i32), ^bb4 {handshake.name = "cond_br0"}
  ^bb4:  // pred: ^bb3
    %c8_i32 = arith.constant {handshake.name = "constant17"} 8 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant18"} 1 : i32
    %24 = arith.addi %3, %c1_i32_2 {handshake.name = "addi5"} : i32
    %25 = arith.cmpi ult, %24, %c8_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %25, ^bb2(%24 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    %c4_i32 = arith.constant {handshake.name = "constant19"} 4 : i32
    %c1_i32_3 = arith.constant {handshake.name = "constant20"} 1 : i32
    %26 = arith.addi %0, %c1_i32_3 {handshake.name = "addi6"} : i32
    %27 = arith.cmpi ult, %26, %c4_i32 {handshake.name = "cmpi2"} : i32
    cf.cond_br %27, ^bb1(%26 : i32), ^bb6 {handshake.name = "cond_br2"}
  ^bb6:  // pred: ^bb5
    return {handshake.name = "return0"}
  }
}


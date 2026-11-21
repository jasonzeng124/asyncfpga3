module {
  func.func @matvec(%arg0: memref<10000xi32> {handshake.arg_name = "m"}, %arg1: memref<100xi32> {handshake.arg_name = "v"}, %arg2: memref<100xi32> {handshake.arg_name = "out"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant7"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    cf.br ^bb2(%c0_i32_0, %c0_i32_0 : i32, i32) {handshake.name = "br1"}
  ^bb2(%2: i32, %3: i32):  // 2 preds: ^bb1, ^bb2
    %c100_i32 = arith.constant {handshake.name = "constant8"} 100 : i32
    %c1_i32 = arith.constant {handshake.name = "constant9"} 1 : i32
    %c6_i64 = arith.constant {handshake.name = "constant10"} 6 : i64
    %c5_i64 = arith.constant {handshake.name = "constant11"} 5 : i64
    %c2_i64 = arith.constant {handshake.name = "constant12"} 2 : i64
    %4 = arith.extui %2 {handshake.name = "extui1"} : i32 to i64
    %5 = arith.index_cast %4 {handshake.name = "index_cast0"} : i64 to index
    %6 = memref.load %arg1[%5] {handshake.name = "load0"} : memref<100xi32>
    %7 = arith.extui %2 {handshake.name = "extui2"} : i32 to i64
    %8 = arith.shli %1, %c2_i64 {handshake.name = "shli0"} : i64
    %9 = arith.shli %1, %c5_i64 {handshake.name = "shli1"} : i64
    %10 = arith.shli %1, %c6_i64 {handshake.name = "shli2"} : i64
    %11 = arith.addi %9, %10 {handshake.name = "addi4"} : i64
    %12 = arith.addi %8, %11 {handshake.name = "addi5"} : i64
    %13 = arith.addi %12, %7 {handshake.name = "addi0"} : i64
    %14 = arith.index_cast %13 {handshake.name = "index_cast1"} : i64 to index
    %15 = memref.load %arg0[%14] {handshake.name = "load1"} : memref<10000xi32>
    %16 = arith.muli %6, %15 {handshake.name = "muli1"} : i32
    %17 = arith.addi %3, %16 {handshake.name = "addi1"} : i32
    %18 = arith.addi %2, %c1_i32 {handshake.name = "addi2"} : i32
    %19 = arith.cmpi ult, %18, %c100_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %19, ^bb2(%18, %17 : i32, i32), ^bb3(%17 : i32) {handshake.name = "cond_br0"}
  ^bb3(%20: i32):  // pred: ^bb2
    %c100_i32_1 = arith.constant {handshake.name = "constant13"} 100 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant14"} 1 : i32
    %21 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    %22 = arith.index_cast %21 {handshake.name = "index_cast2"} : i64 to index
    memref.store %20, %arg2[%22] {handshake.name = "store2"} : memref<100xi32>
    %23 = arith.addi %0, %c1_i32_2 {handshake.name = "addi3"} : i32
    %24 = arith.cmpi ult, %23, %c100_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %24, ^bb1(%23 : i32), ^bb4(%20 : i32) {handshake.name = "cond_br1"}
  ^bb4(%25: i32):  // pred: ^bb3
    return {handshake.name = "return0"} %25 : i32
  }
}


module {
  memref.global "private" constant @constant_array : memref<9xi32> = dense<[1, 2, 3, 4, 5, 6, 7, 8, 9]> {alignment = 16 : i64, handshake.name = "global0"}
  func.func @test_constant_array(%arg0: memref<9xi32> {handshake.arg_name = "di"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = memref.get_global @constant_array : memref<9xi32> {handshake.name = "get_global0"}
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32) {handshake.name = "br0"}
  ^bb1(%1: i32, %2: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant5"} 0 : i32
    %3 = arith.extui %2 {handshake.name = "extui0"} : i32 to i64
    %4 = arith.extui %2 {handshake.name = "extui1"} : i32 to i64
    cf.br ^bb2(%c0_i32_0, %1 : i32, i32) {handshake.name = "br1"}
  ^bb2(%5: i32, %6: i32):  // 2 preds: ^bb1, ^bb2
    %c3_i32 = arith.constant {handshake.name = "constant6"} 3 : i32
    %c1_i32 = arith.constant {handshake.name = "constant7"} 1 : i32
    %c1_i64 = arith.constant {handshake.name = "constant8"} 1 : i64
    %7 = arith.extui %5 {handshake.name = "extui2"} : i32 to i64
    %8 = arith.shli %3, %c1_i64 {handshake.name = "shli0"} : i64
    %9 = arith.addi %3, %8 {handshake.name = "addi2"} : i64
    %10 = arith.addi %9, %7 {handshake.name = "addi0"} : i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast0"} : i64 to index
    %12 = memref.load %arg0[%11] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<9xi32>
    %13 = arith.extui %5 {handshake.name = "extui3"} : i32 to i64
    %14 = arith.shli %4, %c1_i64 {handshake.name = "shli1"} : i64
    %15 = arith.addi %4, %14 {handshake.name = "addi7"} : i64
    %16 = arith.addi %15, %13 {handshake.name = "addi1"} : i64
    %17 = arith.index_cast %16 {handshake.name = "index_cast1"} : i64 to index
    %18 = memref.load %0[%17] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<9xi32>
    %19 = arith.addi %12, %18 {handshake.name = "addi3"} : i32
    %20 = arith.addi %6, %19 {handshake.name = "addi4"} : i32
    %21 = arith.addi %5, %c1_i32 {handshake.name = "addi5"} : i32
    %22 = arith.cmpi ult, %21, %c3_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %22, ^bb2(%21, %20 : i32, i32), ^bb3(%20 : i32) {handshake.name = "cond_br0"}
  ^bb3(%23: i32):  // pred: ^bb2
    %c3_i32_1 = arith.constant {handshake.name = "constant9"} 3 : i32
    %c1_i32_2 = arith.constant {handshake.name = "constant10"} 1 : i32
    %24 = arith.addi %2, %c1_i32_2 {handshake.name = "addi6"} : i32
    %25 = arith.cmpi ult, %24, %c3_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %25, ^bb1(%23, %24 : i32, i32), ^bb4(%23 : i32) {handshake.name = "cond_br1"}
  ^bb4(%26: i32):  // pred: ^bb3
    return {handshake.name = "return0"} %26 : i32
  }
}


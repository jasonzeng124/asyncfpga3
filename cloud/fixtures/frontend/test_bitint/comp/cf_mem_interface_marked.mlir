module {
  memref.global "private" constant @__const.main.arr : memref<10xi16> = dense<[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]> {alignment = 16 : i64, handshake.name = "global0"}
  memref.global "private" constant @__const.main.weight : memref<10xi5> = dense<[10, 9, 8, 7, 6, 5, 4, 3, 2, 1]> {alignment = 1 : i64, handshake.name = "global1"}
  func.func @test_bitint(%arg0: memref<10xi16> {handshake.arg_name = "arr"}, %arg1: memref<10xi5> {handshake.arg_name = "weight"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32, %c0_i32 : i32, i32) {handshake.name = "br0"}
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb1
    %c10_i32 = arith.constant {handshake.name = "constant3"} 10 : i32
    %c1_i32 = arith.constant {handshake.name = "constant4"} 1 : i32
    %2 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<10xi16>
    %5 = arith.extui %4 {handshake.name = "extui1"} : i16 to i21
    %6 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %7 = arith.index_cast %6 {handshake.name = "index_cast1"} : i64 to index
    %8 = memref.load %arg1[%7] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load1"} : memref<10xi5>
    %9 = arith.extui %8 {handshake.name = "extui3"} : i5 to i21
    %10 = arith.muli %5, %9 {handshake.name = "muli0"} : i21
    %11 = arith.extui %10 {handshake.name = "extui4"} : i21 to i32
    %12 = arith.addi %1, %11 {handshake.name = "addi0"} : i32
    %13 = arith.addi %0, %c1_i32 {handshake.name = "addi1"} : i32
    %14 = arith.cmpi ult, %13, %c10_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %14, ^bb1(%13, %12 : i32, i32), ^bb2(%12 : i32) {handshake.name = "cond_br0"}
  ^bb2(%15: i32):  // pred: ^bb1
    return {handshake.name = "return0"} %15 : i32
  }
}


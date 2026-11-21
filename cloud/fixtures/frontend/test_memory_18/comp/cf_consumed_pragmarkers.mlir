module {
  func.func @test_memory_18(%arg0: memref<4xi32> {handshake.arg_name = "x"}, %arg1: memref<4xi32> {handshake.arg_name = "y"}) {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    cf.br ^bb1(%c1_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c4_i32 = arith.constant {handshake.name = "constant3"} 4 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant4"} 1 : i32
    %c0 = arith.constant {handshake.name = "constant5"} 0 : index
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {handshake.name = "load0"} : memref<4xi32>
    %4 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %5 = arith.index_cast %4 {handshake.name = "index_cast1"} : i64 to index
    %6 = memref.load %arg1[%5] {handshake.name = "load1"} : memref<4xi32>
    %7 = arith.muli %3, %6 {handshake.name = "muli0"} : i32
    %8 = memref.load %arg0[%c0] {handshake.name = "load2"} : memref<4xi32>
    %9 = arith.addi %7, %8 {handshake.name = "addi0"} : i32
    %10 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %11 = arith.index_cast %10 {handshake.name = "index_cast2"} : i64 to index
    memref.store %9, %arg0[%11] {handshake.name = "store3"} : memref<4xi32>
    %12 = arith.addi %0, %c1_i32_0 {handshake.name = "addi1"} : i32
    %13 = arith.cmpi ult, %12, %c4_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %13, ^bb1(%12 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    return {handshake.name = "return0"}
  }
}


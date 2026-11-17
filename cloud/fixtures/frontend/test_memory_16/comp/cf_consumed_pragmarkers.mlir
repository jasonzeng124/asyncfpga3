module {
  func.func @test_memory_16(%arg0: memref<4xi32> {handshake.arg_name = "a"}, %arg1: memref<4xi32> {handshake.arg_name = "b"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb4
    %c5_i32 = arith.constant {handshake.name = "constant5"} 5 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg1[%2] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<4xi32>
    %4 = arith.cmpi sgt, %3, %c5_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %4, ^bb2, ^bb3 {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %c0_i32_0 = arith.constant {handshake.name = "constant6"} 0 : i32
    %5 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %6 = arith.index_cast %5 {handshake.name = "index_cast1"} : i64 to index
    memref.store %c0_i32_0, %arg1[%6] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<4xi32>
    cf.br ^bb4(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb3:  // pred: ^bb1
    %c-1_i32 = arith.constant {handshake.name = "constant7"} -1 : i32
    %7 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %8 = arith.index_cast %7 {handshake.name = "index_cast2"} : i64 to index
    %9 = memref.load %arg0[%8] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : memref<4xi32>
    %10 = arith.addi %9, %c-1_i32 {handshake.name = "addi0"} : i32
    cf.br ^bb4(%10 : i32) {handshake.name = "br2"}
  ^bb4(%11: i32):  // 2 preds: ^bb2, ^bb3
    %c4_i32 = arith.constant {handshake.name = "constant8"} 4 : i32
    %c1_i32 = arith.constant {handshake.name = "constant9"} 1 : i32
    %12 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    %13 = arith.index_cast %12 {handshake.name = "index_cast3"} : i64 to index
    memref.store %11, %arg0[%13] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<4xi32>
    %14 = arith.addi %0, %c1_i32 {handshake.name = "addi1"} : i32
    %15 = arith.cmpi ult, %14, %c4_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %15, ^bb1(%14 : i32), ^bb5 {handshake.name = "cond_br1"}
  ^bb5:  // pred: ^bb4
    return {handshake.name = "return0"}
  }
}


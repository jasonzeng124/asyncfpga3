module {
  func.func @test_memory_13(%arg0: memref<4xi32> {handshake.arg_name = "a"}, %arg1: memref<4xi32> {handshake.arg_name = "b"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c5_i32 = arith.constant {handshake.name = "constant4"} 5 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<4xi32>
    %4 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %5 = arith.index_cast %4 {handshake.name = "index_cast1"} : i64 to index
    %6 = memref.load %arg1[%5] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load1"} : memref<4xi32>
    %7 = arith.cmpi sgt, %6, %c5_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %7, ^bb2, ^bb3(%3 : i32) {handshake.name = "cond_br0"}
  ^bb2:  // pred: ^bb1
    %c0_i32_0 = arith.constant {handshake.name = "constant5"} 0 : i32
    %8 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast2"} : i64 to index
    memref.store %c0_i32_0, %arg1[%9] {handshake.deps = #handshake<deps[{dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<4xi32>
    cf.br ^bb3(%c0_i32_0 : i32) {handshake.name = "br1"}
  ^bb3(%10: i32):  // 2 preds: ^bb1, ^bb2
    %c4_i32 = arith.constant {handshake.name = "constant6"} 4 : i32
    %c1_i32 = arith.constant {handshake.name = "constant7"} 1 : i32
    %11 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    %12 = arith.index_cast %11 {handshake.name = "index_cast3"} : i64 to index
    memref.store %10, %arg0[%12] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<4xi32>
    %13 = arith.addi %0, %c1_i32 {handshake.name = "addi0"} : i32
    %14 = arith.cmpi ult, %13, %c4_i32 {handshake.name = "cmpi1"} : i32
    cf.cond_br %14, ^bb1(%13 : i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}


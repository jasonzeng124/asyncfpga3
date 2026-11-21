module {
  func.func @test_memory_11(%arg0: memref<4xi32> {handshake.arg_name = "a"}) {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    cf.br ^bb1(%c1_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c4_i32 = arith.constant {handshake.name = "constant3"} 4 : i32
    %c-1_i32 = arith.constant {handshake.name = "constant4"} -1 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant5"} 1 : i32
    %1 = arith.addi %0, %c-1_i32 {handshake.name = "addi0"} : i32
    %2 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<4xi32>
    %5 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %6 = arith.index_cast %5 {handshake.name = "index_cast1"} : i64 to index
    %7 = memref.load %arg0[%6] {handshake.name = "load1"} : memref<4xi32>
    %8 = arith.addi %4, %7 {handshake.name = "addi1"} : i32
    %9 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %10 = arith.index_cast %9 {handshake.name = "index_cast2"} : i64 to index
    memref.store %8, %arg0[%10] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<4xi32>
    %11 = arith.addi %0, %c1_i32_0 {handshake.name = "addi2"} : i32
    %12 = arith.cmpi ult, %11, %c4_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %12, ^bb1(%11 : i32), ^bb2(%c1_i32_0 : i32) {handshake.name = "cond_br0"}
  ^bb2(%13: i32):  // 2 preds: ^bb1, ^bb2
    %c4_i32_1 = arith.constant {handshake.name = "constant6"} 4 : i32
    %c-1_i32_2 = arith.constant {handshake.name = "constant7"} -1 : i32
    %c1_i32_3 = arith.constant {handshake.name = "constant8"} 1 : i32
    %14 = arith.addi %13, %c-1_i32_2 {handshake.name = "addi3"} : i32
    %15 = arith.extui %14 {handshake.name = "extui3"} : i32 to i64
    %16 = arith.index_cast %15 {handshake.name = "index_cast3"} : i64 to index
    %17 = memref.load %arg0[%16] {handshake.name = "load3"} : memref<4xi32>
    %18 = arith.extui %13 {handshake.name = "extui4"} : i32 to i64
    %19 = arith.index_cast %18 {handshake.name = "index_cast4"} : i64 to index
    memref.store %17, %arg0[%19] {handshake.deps = #handshake<deps[{dstAccess : "store2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store4"} : memref<4xi32>
    %20 = arith.addi %13, %c1_i32_3 {handshake.name = "addi4"} : i32
    %21 = arith.cmpi ult, %20, %c4_i32_1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %21, ^bb2(%20 : i32), ^bb3 {handshake.name = "cond_br1"}
  ^bb3:  // pred: ^bb2
    return {handshake.name = "return0"}
  }
}


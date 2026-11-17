module {
  func.func @histogram(%arg0: memref<1000xi32>, %arg1: memref<1000xf32>, %arg2: memref<1000xf32>, %arg3: i32) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %0 = arith.cmpi slt, %c0_i32, %arg3 : i32
    cf.cond_br %0, ^bb1(%c0_i32 : i32), ^bb2
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.extui %1 : i32 to i64
    %3 = arith.index_cast %2 : i64 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<1000xi32>
    %5 = arith.extui %1 : i32 to i64
    %6 = arith.index_cast %5 : i64 to index
    %7 = memref.load %arg1[%6] {handshake.name = "load1"} : memref<1000xf32>
    %8 = arith.extsi %4 : i32 to i64
    %9 = arith.index_cast %8 : i64 to index
    %10 = memref.load %arg2[%9] {handshake.deps = #handshake<deps[{dstAccess : "store3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load2"} : memref<1000xf32>
    %11 = arith.addf %10, %7 : f32
    %12 = arith.extsi %4 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    memref.store %11, %arg2[%13] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<1000xf32>
    %14 = arith.addi %1, %c1_i32 : i32
    %15 = arith.cmpi slt, %14, %arg3 : i32
    cf.cond_br %15, ^bb1(%14 : i32), ^bb2
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return
  }
}

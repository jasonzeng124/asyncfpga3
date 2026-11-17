module {
  memref.global "private" constant @".str" : memref<22xi8> = dense<[78, 111, 32, 116, 114, 105, 118, 105, 97, 108, 32, 108, 111, 111, 112, 32, 98, 111, 117, 110, 100, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.1" : memref<53xi8> = dense<[40, 40, 40, 110, 32, 62, 61, 32, 50, 41, 32, 33, 61, 32, 48, 41, 32, 38, 32, 40, 40, 34, 78, 111, 32, 116, 114, 105, 118, 105, 97, 108, 32, 108, 111, 111, 112, 32, 98, 111, 117, 110, 100, 34, 41, 32, 33, 61, 32, 48, 41, 41, 0]> {alignment = 1 : i64}
  memref.global "private" constant @".str.2" : memref<44xi8> = dense<[98, 117, 105, 108, 100, 47, 102, 114, 111, 110, 116, 101, 110, 100, 47, 108, 111, 111, 112, 95, 97, 114, 114, 97, 121, 47, 99, 111, 109, 112, 47, 108, 111, 111, 112, 95, 97, 114, 114, 97, 121, 46, 99, 0]> {alignment = 1 : i64}
  memref.global "private" constant @__PRETTY_FUNCTION__.main : memref<15xi8> = dense<[105, 110, 116, 32, 109, 97, 105, 110, 40, 118, 111, 105, 100, 41, 0]> {alignment = 1 : i64}
  func.func @loop_array(%arg0: i32, %arg1: i32, %arg2: memref<10xi32>) {
    %c1_i32 = arith.constant 1 : i32
    %c-1_i32 = arith.constant -1 : i32
    %0 = arith.cmpi slt, %c1_i32, %arg0 : i32
    cf.cond_br %0, ^bb1(%c1_i32 : i32), ^bb2
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %2 = arith.addi %1, %c-1_i32 : i32
    %3 = arith.extsi %2 : i32 to i64
    %4 = arith.index_cast %3 : i64 to index
    %5 = memref.load %arg2[%4] {handshake.name = "load0"} : memref<10xi32>
    %6 = arith.addi %5, %arg1 : i32
    %7 = arith.extui %1 : i32 to i64
    %8 = arith.index_cast %7 : i64 to index
    memref.store %6, %arg2[%8] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<10xi32>
    %9 = arith.addi %1, %c1_i32 : i32
    %10 = arith.cmpi slt, %9, %arg0 : i32
    cf.cond_br %10, ^bb1(%9 : i32), ^bb2
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return
  }
}

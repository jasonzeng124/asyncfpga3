module {
  memref.global "private" constant @".str" : memref<22xi8> = dense<[78, 111, 32, 116, 114, 105, 118, 105, 97, 108, 32, 108, 111, 111, 112, 32, 98, 111, 117, 110, 100, 0]> {alignment = 1 : i64, handshake.name = "global0"}
  memref.global "private" constant @".str.1" : memref<53xi8> = dense<[40, 40, 40, 110, 32, 62, 61, 32, 50, 41, 32, 33, 61, 32, 48, 41, 32, 38, 32, 40, 40, 34, 78, 111, 32, 116, 114, 105, 118, 105, 97, 108, 32, 108, 111, 111, 112, 32, 98, 111, 117, 110, 100, 34, 41, 32, 33, 61, 32, 48, 41, 41, 0]> {alignment = 1 : i64, handshake.name = "global1"}
  memref.global "private" constant @".str.2" : memref<44xi8> = dense<[98, 117, 105, 108, 100, 47, 102, 114, 111, 110, 116, 101, 110, 100, 47, 108, 111, 111, 112, 95, 97, 114, 114, 97, 121, 47, 99, 111, 109, 112, 47, 108, 111, 111, 112, 95, 97, 114, 114, 97, 121, 46, 99, 0]> {alignment = 1 : i64, handshake.name = "global2"}
  memref.global "private" constant @__PRETTY_FUNCTION__.main : memref<15xi8> = dense<[105, 110, 116, 32, 109, 97, 105, 110, 40, 118, 111, 105, 100, 41, 0]> {alignment = 1 : i64, handshake.name = "global3"}
  func.func @loop_array(%arg0: i32 {handshake.arg_name = "n"}, %arg1: i32 {handshake.arg_name = "k"}, %arg2: memref<10xi32> {handshake.arg_name = "c"}) {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    %0 = arith.cmpi sgt, %arg0, %c1_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c1_i32 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %c-1_i32 = arith.constant {handshake.name = "constant2"} -1 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant3"} 1 : i32
    %2 = arith.addi %1, %c-1_i32 {handshake.name = "addi0"} : i32
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i32 to index
    %4 = memref.load %arg2[%3] {handshake.name = "load0"} : memref<10xi32>
    %5 = arith.addi %4, %arg1 {handshake.name = "addi1"} : i32
    %6 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %7 = arith.index_cast %6 {handshake.name = "index_cast1"} : i64 to index
    memref.store %5, %arg2[%7] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<10xi32>
    %8 = arith.addi %1, %c1_i32_0 {handshake.name = "addi2"} : i32
    %9 = arith.cmpi slt, %8, %arg0 {handshake.name = "cmpi1"} : i32
    cf.cond_br %9, ^bb1(%8 : i32), ^bb2 {handshake.name = "cond_br1"}
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"}
  }
}


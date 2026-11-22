module {
  func.func @test_memory_9(%arg0: memref<4xi32> {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "n"}) {
    %c1_i32 = arith.constant {handshake.name = "constant0"} 1 : i32
    %0 = arith.cmpi sgt, %arg1, %c1_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1(%c1_i32 : i32), ^bb2 {handshake.name = "cond_br0"}
  ^bb1(%1: i32):  // 2 preds: ^bb0, ^bb1
    %c-1_i32 = arith.constant {handshake.name = "constant4"} -1 : i32
    %c1_i32_0 = arith.constant {handshake.name = "constant5"} 1 : i32
    %c2_i32 = arith.constant {handshake.name = "constant6"} 2 : i32
    %2 = arith.addi %1, %c-1_i32 {handshake.name = "addi0"} : i32
    %3 = arith.index_cast %2 {handshake.name = "index_cast0"} : i32 to index
    %4 = memref.load %arg0[%3] {handshake.name = "load0"} : memref<4xi32>
    %5 = arith.shli %4, %c2_i32 {handshake.name = "shli0"} : i32
    %6 = arith.addi %4, %5 {handshake.name = "addi2"} : i32
    %7 = arith.extui %1 {handshake.name = "extui0"} : i32 to i64
    %8 = arith.index_cast %7 {handshake.name = "index_cast1"} : i64 to index
    memref.store %6, %arg0[%8] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store1"} : memref<4xi32>
    %9 = arith.addi %1, %c1_i32_0 {handshake.name = "addi1"} : i32
    %10 = arith.cmpi slt, %9, %arg1 {handshake.name = "cmpi1"} : i32
    cf.cond_br %10, ^bb1(%9 : i32), ^bb2 {handshake.name = "cond_br1"}
  ^bb2:  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"}
  }
}


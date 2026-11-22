module {
  func.func @while_loop_2(%arg0: memref<1000xi32> {handshake.arg_name = "a"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant3"} 1 : i32
    %c0_i32_0 = arith.constant {handshake.name = "constant4"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg0[%2] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "load0"} : memref<1000xi32>
    %4 = arith.cmpi eq, %3, %c0_i32_0 {handshake.name = "cmpi0"} : i32
    %5 = arith.addi %0, %c1_i32 {handshake.name = "addi0"} : i32
    cf.cond_br %4, ^bb2(%0 : i32), ^bb1(%5 : i32) {handshake.name = "cond_br0"}
  ^bb2(%6: i32):  // pred: ^bb1
    %c0 = arith.constant {handshake.name = "constant5"} 0 : index
    memref.store %6, %arg0[%c0] {handshake.name = "store1"} : memref<1000xi32>
    return {handshake.name = "return0"}
  }
}


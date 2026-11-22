module {
  func.func @while_loop_3(%arg0: memref<100xi32> {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "bound"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %c1_i32 = arith.constant {handshake.name = "constant3"} 1 : i32
    %1 = arith.muli %0, %0 {handshake.name = "muli0"} : i32
    %2 = arith.cmpi slt, %1, %arg1 {handshake.name = "cmpi0"} : i32
    %3 = arith.addi %0, %c1_i32 {handshake.name = "addi0"} : i32
    cf.cond_br %2, ^bb1(%3 : i32), ^bb2(%0 : i32) {handshake.name = "cond_br0"}
  ^bb2(%4: i32):  // pred: ^bb1
    %c0 = arith.constant {handshake.name = "constant4"} 0 : index
    memref.store %4, %arg0[%c0] {handshake.name = "store0"} : memref<100xi32>
    return {handshake.name = "return0"}
  }
}


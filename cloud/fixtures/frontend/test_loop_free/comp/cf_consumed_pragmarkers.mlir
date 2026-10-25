module {
  func.func @test_loop_free(%arg0: i32 {handshake.arg_name = "a"}, %arg1: i32 {handshake.arg_name = "b"}, %arg2: i32 {handshake.arg_name = "c"}, %arg3: i32 {handshake.arg_name = "d"}) -> i32 {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    %0 = arith.cmpi sgt, %arg0, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %0, ^bb1, ^bb2 {handshake.name = "cond_br0"}
  ^bb1:  // pred: ^bb0
    %1 = arith.addi %arg1, %arg2 {handshake.name = "addi0"} : i32
    %2 = arith.addi %1, %arg3 {handshake.name = "addi1"} : i32
    cf.br ^bb3(%2 : i32) {handshake.name = "br0"}
  ^bb2:  // pred: ^bb0
    %c0_i32_0 = arith.constant {handshake.name = "constant1"} 0 : i32
    %3 = arith.cmpi slt, %arg1, %c0_i32_0 {handshake.name = "cmpi1"} : i32
    %4 = arith.addi %arg0, %arg3 {handshake.name = "addi2"} : i32
    %5 = arith.select %3, %4, %arg0 {handshake.name = "select0"} : i32
    cf.br ^bb3(%5 : i32) {handshake.name = "br1"}
  ^bb3(%6: i32):  // 2 preds: ^bb1, ^bb2
    return {handshake.name = "return0"} %6 : i32
  }
}


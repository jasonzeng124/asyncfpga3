module {
  func.func @test_loop_free(%arg0: i32, %arg1: i32, %arg2: i32, %arg3: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %0 = arith.cmpi sgt, %arg0, %c0_i32 : i32
    cf.cond_br %0, ^bb1, ^bb2
  ^bb1:  // pred: ^bb0
    %1 = arith.addi %arg1, %arg2 : i32
    %2 = arith.addi %1, %arg3 : i32
    cf.br ^bb3(%2 : i32)
  ^bb2:  // pred: ^bb0
    %3 = arith.cmpi slt, %arg1, %c0_i32 : i32
    %4 = arith.addi %arg0, %arg3 : i32
    %5 = arith.select %3, %4, %arg0 : i32
    cf.br ^bb3(%5 : i32)
  ^bb3(%6: i32):  // 2 preds: ^bb1, ^bb2
    return %6 : i32
  }
}

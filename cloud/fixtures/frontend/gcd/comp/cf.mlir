module {
  func.func @gcd(%arg0: i32, %arg1: i32) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c-1_i32 = arith.constant -1 : i32
    %0 = arith.cmpi eq, %arg0, %c0_i32 : i32
    cf.cond_br %0, ^bb13(%arg1 : i32), ^bb1
  ^bb1:  // pred: ^bb0
    %1 = arith.cmpi eq, %arg1, %c0_i32 : i32
    cf.cond_br %1, ^bb13(%arg0 : i32), ^bb2
  ^bb2:  // pred: ^bb1
    %2 = arith.ori %arg0, %arg1 : i32
    %3 = arith.andi %2, %c1_i32 : i32
    %4 = arith.cmpi eq, %3, %c0_i32 : i32
    cf.cond_br %4, ^bb3(%arg0, %arg1, %c0_i32 : i32, i32, i32), ^bb4(%c0_i32, %arg1, %arg0 : i32, i32, i32)
  ^bb3(%5: i32, %6: i32, %7: i32):  // 2 preds: ^bb2, ^bb3
    %8 = arith.shrsi %5, %c1_i32 : i32
    %9 = arith.shrsi %6, %c1_i32 : i32
    %10 = arith.addi %7, %c1_i32 : i32
    %11 = arith.ori %8, %9 : i32
    %12 = arith.andi %11, %c1_i32 : i32
    %13 = arith.cmpi eq, %12, %c0_i32 : i32
    cf.cond_br %13, ^bb3(%8, %9, %10 : i32, i32, i32), ^bb4(%10, %9, %8 : i32, i32, i32)
  ^bb4(%14: i32, %15: i32, %16: i32):  // 2 preds: ^bb2, ^bb3
    cf.br ^bb5(%16 : i32)
  ^bb5(%17: i32):  // 2 preds: ^bb4, ^bb5
    %18 = arith.cmpi slt, %17, %c1_i32 : i32
    %19 = arith.andi %17, %c1_i32 : i32
    %20 = arith.cmpi ne, %19, %c0_i32 : i32
    %21 = arith.ori %20, %18 : i1
    %22 = arith.shrsi %17, %c1_i32 : i32
    cf.cond_br %21, ^bb6(%17 : i32), ^bb5(%22 : i32)
  ^bb6(%23: i32):  // pred: ^bb5
    cf.br ^bb7(%15 : i32)
  ^bb7(%24: i32):  // 2 preds: ^bb6, ^bb7
    %25 = arith.cmpi slt, %24, %c1_i32 : i32
    %26 = arith.andi %24, %c1_i32 : i32
    %27 = arith.cmpi ne, %26, %c0_i32 : i32
    %28 = arith.ori %27, %25 : i1
    %29 = arith.shrsi %24, %c1_i32 : i32
    cf.cond_br %28, ^bb8(%24 : i32), ^bb7(%29 : i32)
  ^bb8(%30: i32):  // pred: ^bb7
    %31 = arith.cmpi eq, %23, %c0_i32 : i32
    cf.cond_br %31, ^bb12(%30 : i32), ^bb10(%23, %30 : i32, i32)
  ^bb9(%32: i32):  // pred: ^bb11
    %33 = arith.cmpi slt, %36, %37 : i32
    %34 = arith.select %33, %36, %37 : i32
    %35 = arith.cmpi eq, %32, %c0_i32 : i32
    cf.cond_br %35, ^bb12(%34 : i32), ^bb10(%32, %34 : i32, i32)
  ^bb10(%36: i32, %37: i32):  // 2 preds: ^bb8, ^bb9
    %38 = arith.subi %36, %37 : i32
    %39 = arith.cmpi sgt, %38, %c-1_i32 : i32
    %40 = arith.subi %c0_i32, %38 : i32
    %41 = arith.select %39, %38, %40 : i32
    cf.br ^bb11(%41 : i32)
  ^bb11(%42: i32):  // 2 preds: ^bb10, ^bb11
    %43 = arith.cmpi slt, %42, %c1_i32 : i32
    %44 = arith.andi %42, %c1_i32 : i32
    %45 = arith.cmpi ne, %44, %c0_i32 : i32
    %46 = arith.ori %45, %43 : i1
    %47 = arith.shrsi %42, %c1_i32 : i32
    cf.cond_br %46, ^bb9(%42 : i32), ^bb11(%47 : i32)
  ^bb12(%48: i32):  // 2 preds: ^bb8, ^bb9
    %49 = arith.shli %48, %14 : i32
    cf.br ^bb13(%49 : i32)
  ^bb13(%50: i32):  // 3 preds: ^bb0, ^bb1, ^bb12
    return %50 : i32
  }
}

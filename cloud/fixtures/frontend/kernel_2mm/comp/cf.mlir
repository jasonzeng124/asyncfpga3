module {
  func.func @kernel_2mm(%arg0: i32, %arg1: i32, %arg2: memref<100xi32>, %arg3: memref<100xi32>, %arg4: memref<100xi32>, %arg5: memref<100xi32>, %arg6: memref<100xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c10_i32 = arith.constant 10 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%3: i32):  // 2 preds: ^bb1, ^bb4
    %4 = arith.extui %3 : i32 to i64
    cf.br ^bb3(%c0_i32, %c0_i32 : i32, i32)
  ^bb3(%5: i32, %6: i32):  // 2 preds: ^bb2, ^bb3
    %7 = arith.extui %5 : i32 to i64
    %c10_i64 = arith.constant 10 : i64
    %8 = arith.muli %1, %c10_i64 : i64
    %9 = arith.addi %8, %7 : i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg3[%10] {handshake.name = "load0"} : memref<100xi32>
    %12 = arith.muli %11, %arg0 : i32
    %13 = arith.extui %5 : i32 to i64
    %c10_i64_0 = arith.constant 10 : i64
    %14 = arith.muli %13, %c10_i64_0 : i64
    %15 = arith.addi %14, %4 : i64
    %16 = arith.index_cast %15 : i64 to index
    %17 = memref.load %arg4[%16] {handshake.name = "load1"} : memref<100xi32>
    %18 = arith.muli %12, %17 : i32
    %19 = arith.addi %6, %18 : i32
    %20 = arith.addi %5, %c1_i32 : i32
    %21 = arith.cmpi ult, %20, %c10_i32 : i32
    cf.cond_br %21, ^bb3(%20, %19 : i32, i32), ^bb4(%19 : i32)
  ^bb4(%22: i32):  // pred: ^bb3
    %23 = arith.extui %3 : i32 to i64
    %c10_i64_1 = arith.constant 10 : i64
    %24 = arith.muli %2, %c10_i64_1 : i64
    %25 = arith.addi %24, %23 : i64
    %26 = arith.index_cast %25 : i64 to index
    memref.store %22, %arg2[%26] {handshake.deps = #handshake<deps[{dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<100xi32>
    %27 = arith.addi %3, %c1_i32 : i32
    %28 = arith.cmpi ult, %27, %c10_i32 : i32
    cf.cond_br %28, ^bb2(%27 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %29 = arith.addi %0, %c1_i32 : i32
    %30 = arith.cmpi ult, %29, %c10_i32 : i32
    cf.cond_br %30, ^bb1(%29 : i32), ^bb6(%c0_i32 : i32)
  ^bb6(%31: i32):  // 2 preds: ^bb5, ^bb10
    %32 = arith.extui %31 : i32 to i64
    %33 = arith.extui %31 : i32 to i64
    %34 = arith.extui %31 : i32 to i64
    cf.br ^bb7(%c0_i32 : i32)
  ^bb7(%35: i32):  // 2 preds: ^bb6, ^bb9
    %36 = arith.extui %35 : i32 to i64
    %c10_i64_2 = arith.constant 10 : i64
    %37 = arith.muli %32, %c10_i64_2 : i64
    %38 = arith.addi %37, %36 : i64
    %39 = arith.index_cast %38 : i64 to index
    %40 = memref.load %arg6[%39] {handshake.name = "load3"} : memref<100xi32>
    %41 = arith.muli %40, %arg1 : i32
    %42 = arith.extui %35 : i32 to i64
    cf.br ^bb8(%c0_i32, %41 : i32, i32)
  ^bb8(%43: i32, %44: i32):  // 2 preds: ^bb7, ^bb8
    %45 = arith.extui %43 : i32 to i64
    %c10_i64_3 = arith.constant 10 : i64
    %46 = arith.muli %33, %c10_i64_3 : i64
    %47 = arith.addi %46, %45 : i64
    %48 = arith.index_cast %47 : i64 to index
    %49 = memref.load %arg2[%48] {handshake.name = "load4"} : memref<100xi32>
    %50 = arith.extui %43 : i32 to i64
    %c10_i64_4 = arith.constant 10 : i64
    %51 = arith.muli %50, %c10_i64_4 : i64
    %52 = arith.addi %51, %42 : i64
    %53 = arith.index_cast %52 : i64 to index
    %54 = memref.load %arg5[%53] {handshake.name = "load5"} : memref<100xi32>
    %55 = arith.muli %49, %54 : i32
    %56 = arith.addi %44, %55 : i32
    %57 = arith.addi %43, %c1_i32 : i32
    %58 = arith.cmpi ult, %57, %c10_i32 : i32
    cf.cond_br %58, ^bb8(%57, %56 : i32, i32), ^bb9(%56 : i32)
  ^bb9(%59: i32):  // pred: ^bb8
    %60 = arith.extui %35 : i32 to i64
    %c10_i64_5 = arith.constant 10 : i64
    %61 = arith.muli %34, %c10_i64_5 : i64
    %62 = arith.addi %61, %60 : i64
    %63 = arith.index_cast %62 : i64 to index
    memref.store %59, %arg6[%63] {handshake.name = "store6"} : memref<100xi32>
    %64 = arith.addi %35, %c1_i32 : i32
    %65 = arith.cmpi ult, %64, %c10_i32 : i32
    cf.cond_br %65, ^bb7(%64 : i32), ^bb10
  ^bb10:  // pred: ^bb9
    %66 = arith.addi %31, %c1_i32 : i32
    %67 = arith.cmpi ult, %66, %c10_i32 : i32
    cf.cond_br %67, ^bb6(%66 : i32), ^bb11
  ^bb11:  // pred: ^bb10
    return
  }
}

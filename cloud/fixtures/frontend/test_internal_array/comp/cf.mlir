module {
  func.func @test_internal_array(%arg0: memref<640xi32>, %arg1: memref<640xi32>, %arg2: memref<640xi32>, %arg3: memref<640xi32>) {
    %c1_i32 = arith.constant 1 : i32
    %c0_i32 = arith.constant 0 : i32
    %c0_i64 = arith.constant 0 : i64
    %c32_i32 = arith.constant 32 : i32
    %c20_i32 = arith.constant 20 : i32
    %alloca = memref.alloca() : memref<640xi32>
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.extui %0 : i32 to i64
    %3 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%c0_i32 : i32)
  ^bb2(%4: i32):  // 2 preds: ^bb1, ^bb2
    %5 = arith.extui %4 : i32 to i64
    %c5_i64 = arith.constant 5 : i64
    %6 = arith.shli %1, %c5_i64 : i64
    %7 = arith.addi %6, %5 : i64
    %8 = arith.index_cast %7 : i64 to index
    %9 = memref.load %arg0[%8] {handshake.name = "load0"} : memref<640xi32>
    %10 = arith.extui %4 : i32 to i64
    %c5_i64_0 = arith.constant 5 : i64
    %11 = arith.shli %2, %c5_i64_0 : i64
    %12 = arith.addi %11, %10 : i64
    %13 = arith.index_cast %12 : i64 to index
    %14 = memref.load %arg1[%13] {handshake.name = "load1"} : memref<640xi32>
    %15 = arith.muli %9, %14 : i32
    %16 = arith.extui %4 : i32 to i64
    %c640_i64 = arith.constant 640 : i64
    %17 = arith.muli %c0_i64, %c640_i64 : i64
    %c5_i64_1 = arith.constant 5 : i64
    %18 = arith.shli %3, %c5_i64_1 : i64
    %19 = arith.addi %18, %16 : i64
    %20 = arith.addi %17, %19 : i64
    %21 = arith.index_cast %20 : i64 to index
    memref.store %15, %alloca[%21] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<640xi32>
    %22 = arith.addi %4, %c1_i32 : i32
    %23 = arith.cmpi ult, %22, %c32_i32 : i32
    cf.cond_br %23, ^bb2(%22 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    %24 = arith.addi %0, %c1_i32 : i32
    %25 = arith.cmpi ult, %24, %c20_i32 : i32
    cf.cond_br %25, ^bb1(%24 : i32), ^bb4(%c0_i32 : i32)
  ^bb4(%26: i32):  // 2 preds: ^bb3, ^bb6
    %27 = arith.extui %26 : i32 to i64
    %28 = arith.extui %26 : i32 to i64
    %29 = arith.extui %26 : i32 to i64
    cf.br ^bb5(%c0_i32 : i32)
  ^bb5(%30: i32):  // 2 preds: ^bb4, ^bb5
    %31 = arith.extui %30 : i32 to i64
    %c640_i64_2 = arith.constant 640 : i64
    %32 = arith.muli %c0_i64, %c640_i64_2 : i64
    %c5_i64_3 = arith.constant 5 : i64
    %33 = arith.shli %27, %c5_i64_3 : i64
    %34 = arith.addi %33, %31 : i64
    %35 = arith.addi %32, %34 : i64
    %36 = arith.index_cast %35 : i64 to index
    %37 = memref.load %alloca[%36] {handshake.name = "load3"} : memref<640xi32>
    %38 = arith.extui %30 : i32 to i64
    %c5_i64_4 = arith.constant 5 : i64
    %39 = arith.shli %28, %c5_i64_4 : i64
    %40 = arith.addi %39, %38 : i64
    %41 = arith.index_cast %40 : i64 to index
    %42 = memref.load %arg2[%41] {handshake.name = "load4"} : memref<640xi32>
    %43 = arith.muli %37, %42 : i32
    %44 = arith.extui %30 : i32 to i64
    %c5_i64_5 = arith.constant 5 : i64
    %45 = arith.shli %29, %c5_i64_5 : i64
    %46 = arith.addi %45, %44 : i64
    %47 = arith.index_cast %46 : i64 to index
    memref.store %43, %arg3[%47] {handshake.name = "store5"} : memref<640xi32>
    %48 = arith.addi %30, %c1_i32 : i32
    %49 = arith.cmpi ult, %48, %c32_i32 : i32
    cf.cond_br %49, ^bb5(%48 : i32), ^bb6
  ^bb6:  // pred: ^bb5
    %50 = arith.addi %26, %c1_i32 : i32
    %51 = arith.cmpi ult, %50, %c20_i32 : i32
    cf.cond_br %51, ^bb4(%50 : i32), ^bb7
  ^bb7:  // pred: ^bb6
    return
  }
}

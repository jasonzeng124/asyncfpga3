module {
  func.func @atax(%arg0: memref<400xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>, %arg3: memref<20xi32>) {
    %c0_i32 = arith.constant 0 : i32
    %c1_i32 = arith.constant 1 : i32
    %c20_i32 = arith.constant 20 : i32
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb5
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg3[%2] {handshake.name = "load0"} : memref<20xi32>
    %4 = arith.extui %0 : i32 to i64
    cf.br ^bb2(%3, %c0_i32 : i32, i32)
  ^bb2(%5: i32, %6: i32):  // 2 preds: ^bb1, ^bb2
    %7 = arith.extui %6 : i32 to i64
    %c20_i64 = arith.constant 20 : i64
    %8 = arith.muli %4, %c20_i64 : i64
    %9 = arith.addi %8, %7 : i64
    %10 = arith.index_cast %9 : i64 to index
    %11 = memref.load %arg0[%10] {handshake.name = "load1"} : memref<400xi32>
    %12 = arith.extui %6 : i32 to i64
    %13 = arith.index_cast %12 : i64 to index
    %14 = memref.load %arg1[%13] {handshake.name = "load2"} : memref<20xi32>
    %15 = arith.muli %11, %14 : i32
    %16 = arith.addi %5, %15 : i32
    %17 = arith.addi %6, %c1_i32 : i32
    %18 = arith.cmpi ult, %17, %c20_i32 : i32
    cf.cond_br %18, ^bb2(%16, %17 : i32, i32), ^bb3(%16 : i32)
  ^bb3(%19: i32):  // pred: ^bb2
    %20 = arith.extui %0 : i32 to i64
    cf.br ^bb4(%c0_i32 : i32)
  ^bb4(%21: i32):  // 2 preds: ^bb3, ^bb4
    %22 = arith.extui %21 : i32 to i64
    %23 = arith.index_cast %22 : i64 to index
    %24 = memref.load %arg2[%23] {handshake.name = "load3"} : memref<20xi32>
    %25 = arith.extui %21 : i32 to i64
    %c20_i64_0 = arith.constant 20 : i64
    %26 = arith.muli %20, %c20_i64_0 : i64
    %27 = arith.addi %26, %25 : i64
    %28 = arith.index_cast %27 : i64 to index
    %29 = memref.load %arg0[%28] {handshake.name = "load4"} : memref<400xi32>
    %30 = arith.muli %29, %19 : i32
    %31 = arith.addi %24, %30 : i32
    %32 = arith.extui %21 : i32 to i64
    %33 = arith.index_cast %32 : i64 to index
    memref.store %31, %arg2[%33] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store5"} : memref<20xi32>
    %34 = arith.addi %21, %c1_i32 : i32
    %35 = arith.cmpi ult, %34, %c20_i32 : i32
    cf.cond_br %35, ^bb4(%34 : i32), ^bb5
  ^bb5:  // pred: ^bb4
    %36 = arith.extui %0 : i32 to i64
    %37 = arith.index_cast %36 : i64 to index
    memref.store %19, %arg3[%37] {handshake.name = "store6"} : memref<20xi32>
    %38 = arith.addi %0, %c1_i32 : i32
    %39 = arith.cmpi ult, %38, %c20_i32 : i32
    cf.cond_br %39, ^bb1(%38 : i32), ^bb6
  ^bb6:  // pred: ^bb5
    return
  }
}

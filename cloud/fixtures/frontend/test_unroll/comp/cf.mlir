module {
  func.func @test_unroll(%arg0: memref<20xi32>, %arg1: memref<20xi32>, %arg2: memref<20xi32>, %arg3: memref<20xi32>) {
    %c1_i32 = arith.constant 1 : i32
    %c0_i32 = arith.constant 0 : i32
    %c0_i64 = arith.constant 0 : i64
    %c20_i32 = arith.constant 20 : i32
    %alloca = memref.alloca() : memref<20xi32>
    cf.br ^bb1(%c0_i32 : i32)
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb1
    %1 = arith.extui %0 : i32 to i64
    %2 = arith.index_cast %1 : i64 to index
    %3 = memref.load %arg0[%2] {handshake.name = "load0"} : memref<20xi32>
    %4 = arith.extui %0 : i32 to i64
    %5 = arith.index_cast %4 : i64 to index
    %6 = memref.load %arg1[%5] {handshake.name = "load1"} : memref<20xi32>
    %7 = arith.muli %3, %6 : i32
    %8 = arith.extui %0 : i32 to i64
    %c20_i64 = arith.constant 20 : i64
    %9 = arith.muli %c0_i64, %c20_i64 : i64
    %10 = arith.addi %9, %8 : i64
    %11 = arith.index_cast %10 : i64 to index
    memref.store %7, %alloca[%11] {handshake.deps = #handshake<deps[{dstAccess : "load3", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store2"} : memref<20xi32>
    %12 = arith.addi %0, %c1_i32 : i32
    %13 = arith.cmpi ult, %12, %c20_i32 : i32
    cf.cond_br %13, ^bb1(%12 : i32), ^bb2(%c0_i32 : i32)
  ^bb2(%14: i32):  // 2 preds: ^bb1, ^bb2
    %15 = arith.extui %14 : i32 to i64
    %c20_i64_0 = arith.constant 20 : i64
    %16 = arith.muli %c0_i64, %c20_i64_0 : i64
    %17 = arith.addi %16, %15 : i64
    %18 = arith.index_cast %17 : i64 to index
    %19 = memref.load %alloca[%18] {handshake.name = "load3"} : memref<20xi32>
    %20 = arith.extui %14 : i32 to i64
    %21 = arith.index_cast %20 : i64 to index
    %22 = memref.load %arg2[%21] {handshake.name = "load4"} : memref<20xi32>
    %23 = arith.muli %19, %22 : i32
    %24 = arith.extui %14 : i32 to i64
    %25 = arith.index_cast %24 : i64 to index
    memref.store %23, %arg3[%25] {handshake.name = "store5"} : memref<20xi32>
    %26 = arith.addi %14, %c1_i32 : i32
    %27 = arith.cmpi ult, %26, %c20_i32 : i32
    cf.cond_br %27, ^bb2(%26 : i32), ^bb3
  ^bb3:  // pred: ^bb2
    return
  }
}

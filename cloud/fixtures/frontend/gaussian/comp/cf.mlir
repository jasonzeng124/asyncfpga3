module {
  func.func @gaussian(%arg0: memref<20xi32>, %arg1: memref<400xi32>) -> i32 {
    %c1_i32 = arith.constant 1 : i32
    %c3230_i32 = arith.constant 3230 : i32
    %c19_i32 = arith.constant 19 : i32
    %c20_i32 = arith.constant 20 : i32
    %c-190_i32 = arith.constant -190 : i32
    %c29070_i32 = arith.constant 29070 : i32
    cf.br ^bb1(%c1_i32, %c3230_i32 : i32, i32)
  ^bb1(%0: i32, %1: i32):  // 2 preds: ^bb0, ^bb5
    %2 = arith.addi %0, %c1_i32 : i32
    %3 = arith.cmpi ult, %2, %c19_i32 : i32
    cf.cond_br %3, ^bb3(%2 : i32), ^bb5
  ^bb2:  // pred: ^bb4
    %4 = arith.addi %6, %c1_i32 : i32
    %5 = arith.cmpi ult, %4, %c19_i32 : i32
    cf.cond_br %5, ^bb3(%4 : i32), ^bb5
  ^bb3(%6: i32):  // 2 preds: ^bb1, ^bb2
    %7 = arith.extui %6 : i32 to i64
    %8 = arith.extui %0 : i32 to i64
    %9 = arith.extui %0 : i32 to i64
    %10 = arith.extui %6 : i32 to i64
    cf.br ^bb4(%c1_i32 : i32)
  ^bb4(%11: i32):  // 2 preds: ^bb3, ^bb4
    %12 = arith.extui %11 : i32 to i64
    %c20_i64 = arith.constant 20 : i64
    %13 = arith.muli %7, %c20_i64 : i64
    %14 = arith.addi %13, %12 : i64
    %15 = arith.index_cast %14 : i64 to index
    %16 = memref.load %arg1[%15] {handshake.name = "load0"} : memref<400xi32>
    %17 = arith.index_cast %8 : i64 to index
    %18 = memref.load %arg0[%17] {handshake.name = "load1"} : memref<20xi32>
    %19 = arith.extui %11 : i32 to i64
    %c20_i64_0 = arith.constant 20 : i64
    %20 = arith.muli %9, %c20_i64_0 : i64
    %21 = arith.addi %20, %19 : i64
    %22 = arith.index_cast %21 : i64 to index
    %23 = memref.load %arg1[%22] {handshake.name = "load2"} : memref<400xi32>
    %24 = arith.muli %18, %23 : i32
    %25 = arith.subi %16, %24 : i32
    %26 = arith.extui %11 : i32 to i64
    %c20_i64_1 = arith.constant 20 : i64
    %27 = arith.muli %10, %c20_i64_1 : i64
    %28 = arith.addi %27, %26 : i64
    %29 = arith.index_cast %28 : i64 to index
    memref.store %25, %arg1[%29] {handshake.deps = #handshake<deps[{dstAccess : "load0", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<400xi32>
    %30 = arith.addi %11, %c1_i32 : i32
    %31 = arith.cmpi ult, %30, %c20_i32 : i32
    cf.cond_br %31, ^bb4(%30 : i32), ^bb2
  ^bb5:  // 2 preds: ^bb1, ^bb2
    %32 = arith.addi %0, %c1_i32 : i32
    %33 = arith.addi %1, %c-190_i32 : i32
    %34 = arith.cmpi ult, %32, %c19_i32 : i32
    cf.cond_br %34, ^bb1(%32, %33 : i32, i32), ^bb6
  ^bb6:  // pred: ^bb5
    return %c29070_i32 : i32
  }
}

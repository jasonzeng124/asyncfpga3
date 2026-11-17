module {
  func.func @triangular(%arg0: memref<10xi32> {handshake.arg_name = "x"}, %arg1: i32 {handshake.arg_name = "n"}, %arg2: memref<100xi32> {handshake.arg_name = "a"}) {
    %c-1_i32 = arith.constant {handshake.name = "constant0"} -1 : i32
    %c0_i32 = arith.constant {handshake.name = "constant1"} 0 : i32
    %0 = arith.addi %arg1, %c-1_i32 {handshake.name = "addi0"} : i32
    %1 = arith.cmpi sgt, %arg1, %c0_i32 {handshake.name = "cmpi0"} : i32
    cf.cond_br %1, ^bb2(%0, %arg1 : i32, i32), ^bb4 {handshake.name = "cond_br0"}
  ^bb1:  // 2 preds: ^bb2, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant6"} 0 : i32
    %c-1_i32_1 = arith.constant {handshake.name = "constant7"} -1 : i32
    %2 = arith.addi %4, %c-1_i32_1 {handshake.name = "addi1"} : i32
    %3 = arith.cmpi sgt, %4, %c0_i32_0 {handshake.name = "cmpi1"} : i32
    cf.cond_br %3, ^bb2(%2, %4 : i32, i32), ^bb4 {handshake.name = "cond_br1"}
  ^bb2(%4: i32, %5: i32):  // 2 preds: ^bb0, ^bb1
    %c-2_i32 = arith.constant {handshake.name = "constant8"} -2 : i32
    %c-1_i32_2 = arith.constant {handshake.name = "constant9"} -1 : i32
    %6 = arith.addi %5, %c-2_i32 {handshake.name = "addi2"} : i32
    %7 = arith.cmpi sgt, %6, %c-1_i32_2 {handshake.name = "cmpi2"} : i32
    cf.cond_br %7, ^bb3(%6 : i32), ^bb1 {handshake.name = "cond_br2"}
  ^bb3(%8: i32):  // 2 preds: ^bb2, ^bb3
    %c-1_i32_3 = arith.constant {handshake.name = "constant10"} -1 : i32
    %c3_i64 = arith.constant {handshake.name = "constant11"} 3 : i64
    %c1_i64 = arith.constant {handshake.name = "constant12"} 1 : i64
    %9 = arith.extsi %8 {handshake.name = "extsi0"} : i32 to i64
    %10 = arith.extsi %4 {handshake.name = "extsi1"} : i32 to i64
    %11 = arith.shli %9, %c1_i64 {handshake.name = "shli0"} : i64
    %12 = arith.shli %9, %c3_i64 {handshake.name = "shli1"} : i64
    %13 = arith.addi %11, %12 {handshake.name = "addi6"} : i64
    %14 = arith.addi %13, %10 {handshake.name = "addi3"} : i64
    %15 = arith.index_cast %14 {handshake.name = "index_cast0"} : i64 to index
    %16 = memref.load %arg2[%15] {handshake.name = "load0"} : memref<100xi32>
    %17 = arith.index_cast %4 {handshake.name = "index_cast1"} : i32 to index
    %18 = memref.load %arg0[%17] {handshake.name = "load1"} : memref<10xi32>
    %19 = arith.muli %16, %18 {handshake.name = "muli1"} : i32
    %20 = arith.extsi %8 {handshake.name = "extsi3"} : i32 to i64
    %21 = arith.extsi %arg1 {handshake.name = "extsi4"} : i32 to i64
    %22 = arith.shli %20, %c1_i64 {handshake.name = "shli2"} : i64
    %23 = arith.shli %20, %c3_i64 {handshake.name = "shli3"} : i64
    %24 = arith.addi %22, %23 {handshake.name = "addi7"} : i64
    %25 = arith.addi %24, %21 {handshake.name = "addi4"} : i64
    %26 = arith.index_cast %25 {handshake.name = "index_cast2"} : i64 to index
    %27 = memref.load %arg2[%26] {handshake.name = "load2"} : memref<100xi32>
    %28 = arith.subi %27, %19 {handshake.name = "subi0"} : i32
    %29 = arith.index_cast %25 {handshake.name = "index_cast3"} : i64 to index
    memref.store %28, %arg2[%29] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}]>, handshake.name = "store3"} : memref<100xi32>
    %30 = arith.addi %8, %c-1_i32_3 {handshake.name = "addi5"} : i32
    %31 = arith.cmpi sgt, %30, %c-1_i32_3 {handshake.name = "cmpi3"} : i32
    cf.cond_br %31, ^bb3(%30 : i32), ^bb1 {handshake.name = "cond_br3"}
  ^bb4:  // 2 preds: ^bb0, ^bb1
    return {handshake.name = "return0"}
  }
}


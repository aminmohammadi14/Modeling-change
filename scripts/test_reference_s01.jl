# آزمون توسعه؛ کاربر برای اجرای فایل یکپارچه به این فایل نیاز ندارد.
using Test
include(joinpath(@__DIR__,"..","versions","REBUILD_S01","run_step01.jl"))
include(joinpath(@__DIR__,"..","versions","REFERENCE_S01","CODE_REFERENCE.jl"))
@testset "Reference rewrite preserves sourced inputs" begin
    expected=REVCSDataStep01.load_case(joinpath(@__DIR__,"..","versions","REBUILD_S01"))
    actual=ReferenceRewriteS01.load_case()
    @test actual.data == expected.data
    @test actual.case == expected.case
    @test actual.sources == expected.sources
    @test ReferenceRewriteS01.profiles(actual)==REVCSDataStep01.profiles(expected)
    @test ReferenceRewriteS01.gamma_factor==0.24
    @test ReferenceRewriteS01.num_tau==96
    @test ReferenceRewriteS01.wt_profile[25]==0.8520
    @test size(ReferenceRewriteS01.Df_period)==(96,9)
    @test_throws ArgumentError ReferenceRewriteS01.require_optimization_ready(actual)
end

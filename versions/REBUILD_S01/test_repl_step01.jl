# بازسازی نشست شلوغ REPL؛ این فایل آزمون نرم‌افزار است و دادهٔ مدل را تغییر نمی‌دهد.
using Test
include("run_step01.jl")
using .REVCSDataStep01
const original_model = REVCSDataStep01

# یک ماژول دیگر عمداً نام همسان صادر می‌کند تا تداخل نام‌های Main بازسازی شود.
module OtherBindings
export load_case, profiles, require_optimization_ready
load_case() = error("نباید از این تابع استفاده شود")
profiles(x) = error("نباید از این تابع استفاده شود")
require_optimization_ready(x) = error("نباید از این تابع استفاده شود")
end
using .OtherBindings

# اجرای دوبارهٔ همان فایل، بدون راه‌اندازی مجدد Julia و بدون تغییر ماژول اصلی.
include("test_step01.jl")
include("test_step01.jl")
@testset "REPL isolation" begin
    @test REVCSDataStep01 === original_model
    @test REVCSDataStep01.load_case().case["scope"]["buses"] == 33
end

# آزمون رگرسیون کوچک برای مستر چندستونی. اعداد این آزمون صرفاً برای آزمایش الگوریتم هستند.
using Test, JuMP, HiGHS
include("REVCS19_FIX20.jl")
const F=REVCSFix20
const C=F.Core20
@testset "multi-column separation and coverage" begin
    mktempdir() do out
        o=(output=out,threads=1,seconds=20.0)
        witness,_=F.g742_fix13_realization("nominal")
        function fac(m)
            z=@variable(m,binary=true)
            return [z],z,()->witness
        end
        function block(m,z)
            x=@variable(m,binary=true)
            @variable(m,binary=true)
            y=@variable(m,lower_bound=0.0)
            @constraint(m,x==z)
            @objective(m,Min,y)
        end
        p(x,y)=C.IntegerPattern([1,2],[x,y])
        gate,u=F.separate20(o,[p(0,0),p(0,1)],fac,block)
        @test gate==:witness && u===witness
        gate,u=F.separate20(o,[p(0,1),p(1,0)],fac,block)
        @test gate==:covered && u===nothing
        @test C.farkas_gate(F.MOI.TIME_LIMIT,false,NaN,Inf)==:unresolved
    end
end
@testset "verified improvement against all saved column costs" begin
    mktempdir() do out
        function builder(u)
            m=Model(HiGHS.Optimizer)
            set_silent(m)
            set_optimizer_attribute(m,"threads",1)
            x=@variable(m,binary=true)
            y=@variable(m,binary=true)
            @constraint(m,x+y>=1)
            @objective(m,Min,x+2y)
            return m
        end
        cols=[C.IntegerPattern([1,2],k) for k in ([0,1],[1,1])]
        row,p=F.price20((output=out,tol=1e-5),builder,nothing,cols)
        @test row.upper≈1.0
        @test p.values==[1,0]
        _,next=F.price20((output=out,tol=1e-5),builder,nothing,[cols;p])
        @test next===nothing
    end
end

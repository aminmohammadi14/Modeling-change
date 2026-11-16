using Test
include(joinpath(@__DIR__,"revcs_planning19.jl"))

@testset "Section IV-B traffic and renewable growth intervals" begin
    @test 1 .+ theta_fc .- theta_err ≈ [1.,1.3,1.8]
    @test 1 .+ theta_fc .+ theta_err ≈ [1.,1.5,2.0]
    @test 1 .+ zeta_fc .- zeta_err ≈ [1.,1.3,1.7]
    @test 1 .+ zeta_fc .+ zeta_err ≈ [1.,1.5,2.0]
    for t in (2,3)
        u=nominal_scenario(t)
        @test validate_scenario(t,u)
        for d in (-1,1)
            v=deepcopy(u);v["theta_t"]=theta_fc[t]+d*theta_err[t]
            v["zeta_t"]=zeta_fc[t]+d*zeta_err[t]
            @test validate_scenario(t,v)
        end
    end
end

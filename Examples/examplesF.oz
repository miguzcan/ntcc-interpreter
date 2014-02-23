%local


   

functor
import

   NtccInterpreter at '../src/NtccInterpreter.ozf'
export

define

   
   Res
   Lvars = [x
            y
            z
            w
            beta
            gamma
            alpha
            rho
            testVar]
   Vars = {MakeRecord var Lvars}
   Vars:::0#1000


    S1 = when(proc{$ Root}
    		Root.current.x>:0
    	     end
    	     next(tell(proc{$ Root}		     
    			  Root.current.x=:Root.residual.x - 1
    			  Root.current.y=:Root.residual.y + 1
    			  Root.current.z=:Root.residual.z
    			  Root.current.w=:Root.residual.w
    		       end)))
   
    S2 = when(proc{$ Root}
    		Root.current.x>:0
    	     end
    	     next(tell(proc{$ Root}		     
    			  Root.current.x=:Root.residual.x - 1
    			  Root.current.z=:Root.residual.z + 1
    			  Root.current.y=:Root.residual.y
    			  Root.current.w=:Root.residual.w
    		       end)))
   
    S3 = when(proc{$ Root}
    		Root.current.w>:0
    	     end
    	     next(tell(proc{$ Root}		     
    			  Root.current.w=:Root.residual.w - 1
    			  Root.current.x=:Root.residual.x + 1
    			  Root.current.y=:Root.residual.y
    			  Root.current.z=:Root.residual.z
                       end)))

   DumbTest = next(tell(proc{$ Root} Root.current.testVar =: 5 end))


   BoundedRep = boundedrep(5 7 tell(proc{$ Root}
                                       Root.current.beta =: 1
                                    end))

   BoundedStar = boundedstar(5 8 tell(proc{$ Root}
                                         Root.current.gamma =: 1
                                      end))

   Nextupn = nextupn(5 tell(proc{$ Root} Root.current.alpha =: 1 end))

   WhenEver = whenever(proc{$ Root} Root.current.alpha >: 0 end tell(proc{$ Root} Root.current.rho=:1 end))

    LocalVar = next(localvar(fun{$ X}    
                                par(nextupn(2 tell(proc{$ Root} {Nth Root.current.list X} =: 6 end)) UnlessP)
                             end))


   PruebaP = tell(proc{$ Root} Root.current.alpha =: 1 end)
   

   UnlessP = unless(proc{$ Root}
                       Root.current.alpha =: 1
                    end
                   tell(proc{$ Root} Root.current.rho =: 1 end))

   Inic = tell(proc{$ Root}
		  Root.current.x =: 3
		  Root.current.y =: 3
		  Root.current.z =: 3
		  Root.current.w =: 3		    
	       end
	      )

   Sump = par(rep(sum(S2 S1 S3)) BoundedRep DumbTest)

  %    System = par(Inic WhenEver LocalVar UnlessP Nextupn BoundedStar Sump)
  %     System = par(Inic WhenEver LocalVar Nextupn BoundedStar Sump)
   System = par(Inic LocalVar Nextupn BoundedStar Sump)

%in
    {NtccInterpreter.simulate [System]
	  Vars%{FD.tuple vars 2 0#10}
	  3
	  'nombre.txt'
	 }
  % {Browse {List.map Res fun{$ X} X end}}
   % {Browse {List.map Res fun{$ X} X.residual.current end}}
end

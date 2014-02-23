%%%
%%% Authors:
%%%   Christian Schulte <schulte@ps.uni-sb.de>
%%%
%%% Copyright:
%%%   Christian Schulte, 1999
%%%
%%% Last change:
%%%   $Date: 2001/07/31 13:47:42 $ by $Author: schulte $
%%%   $Revision: 1.11 $
%%%
%%% This file is part of Mozart, an implementation
%%% of Oz 3
%%%    http://www.mozart-oz.org
%%%
%%% See the file "LICENSE" or
%%%    http://www.mozart-oz.org/LICENSE.html
%%% for information on usage and redistribution
%%% of this file, and for a DISCLAIMER OF ALL
%%% WARRANTIES.
%%%

functor

import 

   Space
   %Lists
   OS
   Ozcar
   Browser
   BootDictionary(waitOr: DictWaitOr)
   at 'x-oz://boot/Dictionary'

   FDB(int:           FdInt
       bool:          FdBool
       'reflect.dom': FdReflectDom)
   at 'x-oz://boot/FDB'

export
   Choice
   Or
   Dis
   Cond
   Not
   Reify
require
   CpSupport(expand:         Expand)
   
prepare

   local
      proc {Skip}
         skip
      end
   in
      fun {Guardify C}
         case {Procedure.arity C}
         of 1 then C
         [] 0 then fun {$} {C} Skip end
         end
      end
   end

   fun {Deref S}
      case S
      of suspended(S)    then {Deref S}
      [] alternatives(_) then stuck
      [] succeeded(S)    then S
      else S
      end
   end
   
   proc {WUHFI}
      {Wait _}
   end

define

   fun {GetDomList X}
      {Expand {FdReflectDom X}}
   end
   
   fun {NewGuard C}
      {Space.new {Guardify C}}
   end
   
   proc {CommitGuard G}
      {{Space.merge G}}
   end
   
   local
            % N number of processes, C processes per se
            % Create a new dictionary in A, 
            % G is a tuple with N-1 #
      proc {Init N C G A} 
         if N>0 then NG={NewGuard C.N} in
            G.N=NG {Dictionary.put A N {Space.askVerbose NG}}
            {Init N-1 C G A}
         end
      end
   in
      % N number of processes, C processes per se
            % G and A two free variables.
      proc {InitGuards N C ?G ?A}
         G={MakeTuple '#' N}
         A={Dictionary.new} % Create a new dictionary in A, 
         {Init N C G A} % G is a tuple with N-1 #
      end
   end

   proc {KillGuards Is G}
      case Is of nil then skip
      [] I|Ir then {Space.kill G.I} {KillGuards Ir G}
      end
   end

   local
      proc {Cond1 C E}
         G={NewGuard C}
      in
         case {Deref {Space.askVerbose G}}
         of failed   then {E}
         [] entailed then {CommitGuard G}
         [] stuck    then {WUHFI}
         end
      end

      fun {Flatten2 Xs}
                     case Xs of nil then nil
                     [] X|Xr then
                        {Append {Flatten2 X} {Flatten2 Xr}}
                     else [Xs]
                     end
      end
      
      proc{RandomCommit C A G}
      %   {Browser.browse C}
         L = {Record.width C}
      %   {Browser.browse L}
         S
         S = {OS.rand} mod L
      in
         if L==1 then {CommitGuard C.1}
         else
         %   {KillGuards {Dictionary.keys A} G}
          %  {List.toTuple g S}
            {CommitGuard C.(S+1)}
         end
      end

      proc {Resolve G A N B E Lst}
         if N==0 then
            if B then
             %  {Browser.browse 'Bool true'}
               if Lst == nil then
               %   {Browser.browse 'Paso el lst nil'}
                 % {KillGuards {Dictionary.keys A} G}
                  {WUHFI}                 
               else Lflatten in
                  {Flatten2 Lst Lflatten} 
                 % {KillGuards {Dictionary.keys A} G}
                  {WUHFI}
                  {RandomCommit {List.toTuple guards Lflatten} A G}                  
               end
            else
          %     {Browser.browse 'Bool false'}
               if Lst == nil then
                  {E}
               else Lflatten                  
               in
                  
             %     {Browser.browse 'llega al RandomCommit'}
                  {Flatten2 Lst Lflatten} 
           %       {Browser.browse  'lista'#Lflatten}
                
                 % {Browser.browse {List.toTuple g Lflatten}}
                  %{Browser.browse {List.toTuple guards Lst}}
                  {RandomCommit {List.toTuple guards Lflatten} A G}                 
               end
            end
         else I={DictWaitOr A} in
            case {Dictionary.get A I}
            of failed    then
              % {Browser.browse 'failed'}   
               {Dictionary.remove A I}
               {Resolve G A N-1 B E Lst}
            [] succeeded(stuck) then
              % {Browser.browse 'stuck'}   
               {Dictionary.remove A I}
               {Space.kill G.I}
               {Resolve G A N-1 true E Lst}
            [] alternatives(_) then
               {Dictionary.remove A I}
               {Space.kill G.I}
             %  {Browser.browse 'alternatives'}   
               {Resolve G A N-1 true E Lst}
            [] succeeded(entailed) then
               {Dictionary.remove A I}
              % {Browser.browse 'succeeded'}        
              % {KillGuards {Dictionary.keys A} G}
         %      {CommitGuard G.I}
              % {Browser.browse Lst}
                {Resolve G A N-1 B E Lst|G.I}
            [] suspended(AI) then
             %  {Browser.browse 'suspended'}      
               {Dictionary.put A I AI}
               {Resolve G A N B E Lst}
            end
         end
      end
   in
      proc {Cond C E}
         case {Width C}
         of 0 then {E}
         [] 1 then {Cond1 C.1 E}
         [] N then G A in
            {InitGuards N C G A} % N number of processes, C processes per se
            % G and A two free variables.
            {Resolve G A N false E nil}
         end
      end
   end
   
   local
      proc {WaitFailed G A N}
         if N>0 then I={DictWaitOr A} in
            case {Dictionary.get A I}
            of failed then
               {Dictionary.remove A I}
               {WaitFailed G A N-1}
            [] suspended(AI) then
               {Dictionary.put A I AI}
               {WaitFailed G A N}
            else
               {WUHFI}
            end
         end
      end
      proc {Resolve G A N}
         if N>1 then I={DictWaitOr A} in
            case {Dictionary.get A I}
            of failed then
               {Dictionary.remove A I}
               {Resolve G A N-1}
            [] suspended(AI) then
               {Dictionary.put A I AI}
               {Resolve G A N}
            else
               {Dictionary.remove A I}
               {WaitFailed G A N-1}
               {CommitGuard G.I}
            end
         else [I]={Dictionary.keys A} in
            {CommitGuard G.I}
         end
      end
      proc {BinaryOr C1 C2}
         G1={NewGuard C1}
         A1={Space.askVerbose G1}
      in
         if {IsDet A1} andthen A1==failed then
            {{{Guardify C2}}}
         else
            G2={NewGuard C2}
            A2={Space.askVerbose G2}
         in
            if {IsDet A2} andthen A2==failed then
               {CommitGuard G1}
            else A={Dictionary.new} in
               {Dictionary.put A 1 A1}
               {Dictionary.put A 2 A2}
               {Resolve G1#G2 A 2}
            end
         end
      end
   in
      proc {Or C}
         case {Width C}
         of 0 then fail
         [] 1 then {{{Guardify C.1}}}
         [] 2 then {BinaryOr C.1 C.2}
         [] N then G A in
            {InitGuards N C G A}
            {Resolve G A N}
         end
      end
   end

   proc {Choice C}
      {C.{Space.choose {Width C}}}
   end

   local
      proc {CommitOrKill G J I ?B}
         if I==J then B={Space.merge G} else {Space.kill G} end
      end
      proc {Control G A J I ?B}
         {WaitOr A I}
         if {IsDet I} then
            {CommitOrKill G J I ?B}
         else
            case A
            of failed       then {FdInt compl(J) I}
            [] merged       then skip
            [] suspended(A) then {Control G A J I ?B}
            else {CommitOrKill G J I ?B}
            end
         end
      end
   in
      proc {Dis C}
         case {Width C}
         of 0 then fail
         [] 1 then {{{Guardify C.1}}}
         [] N then I={FdInt 1#N} B in
            {For 1 N 1 proc {$ J}
                          G={NewGuard C.J}
                       in
                          thread
                             {Control G {Space.askVerbose G} J I ?B}
                          end
                       end}
            if {IsDet I} then skip else A in
               thread
                  {Space.waitStable}
                  A=unit
                  if {IsDet I} then skip else
                     T={List.toTuple '#' {GetDomList I}}
                  in
                     I=T.{Space.choose {Width T}}
                  end
               end
               {Wait A}
            end
            {B}
         end
      end
   end

   proc {Not P}
      S={Space.new proc {$ X} X=unit {P} end}
   in
      thread
         case {Deref {Space.askVerbose S}}
         of failed   then skip
         [] entailed then fail
         [] stuck    then {WUHFI}
         end
      end
   end

   proc {Reify P B}
      S={Space.new proc {$ X} X=unit {P} end}
   in
      {FdBool B}
      thread
         case {Deref {Space.askVerbose S}}
         of failed   then B=0
         [] entailed then B=1
         [] stuck    then {WUHFI}
         [] merged   then skip
         end
      end
      thread
         if B==1 then {Space.merge S _} end
      end
   end
   
end





/*
 Assume that the locations of the Waypoints are already known and it is possible to
 determine the weather at each of them. A satellite could potentially communicate
 this information to the rover.

 Arm and Mast must be down if it is windy, up otherwise.

 Don't go anywhere that has high radiation because it will damage the rover.

 Assume that B has 100 units of radiation in the beginning which decreases by 10 after 
 each time unit that we have to keep track of manually because Dafny can't do real time.
 This is probably not realistic because decay takes a very long time (!).

 Assume that we always have enough battery power to go between Waypoints and operate
 the equipment so we do not model battery power.

 Assume that we run for 200 time steps.

 Assume that it is always windy at A, so keep the mast and the arm down here.
*/

datatype Command = PatrolA | PatrolB | PatrolC | ArmUp | ArmDown | MastUp | MastDown
datatype Environment = Windy | Radiation | Fine
datatype Waypoint = A | B | C |origin

method Main() 
// Main method to get things going and to test the output 
{
    var acts := CuriosityAgent(Wheels.Ready(), Arm.Ready(), Mast.Ready());
    print acts;
}

method CuriosityAgent(wheelsready:bool, armready:bool, mastready:bool) returns (actions: seq<Command>)
ensures (wheelsready && armready && mastready) == false ==> actions ==[];//this is a safety check - if the hardware is not ready then do nothing.
//ensures (wheelsready && armready && mastready) == true ==> |actions| > 0;
//should visit all 3?
//most dangerous last?
//stop as soon as all 3 are visited

{
    var visitA:bool, visitB:bool, visitC:bool;
    actions := [];
    var time := 0;


    if(wheelsready && armready && mastready)
    {
        var current := origin;
        var next, wind, rad, env;

        while(time <=200)
        decreases 200 - time;
        invariant 0 <= time;
        invariant !(current == B  && env == Radiation);//^ runtime check, rover can't be in B if there is radiation
        {
            next := getnextwaypoint(current);
            wind := getWind(next);
            rad := getRad(next, time);
            env := getEnvironment(next, wind, rad);
            
            if(current == A)
            {//keep moving in order once there is no radiation
                if(env == Fine)
                {
                    actions := actions + [PatrolB, ArmUp, MastUp];
                    current := next;
                }
                else if(env == Windy)
                { 
                    actions := actions + [PatrolB, ArmDown, MastDown];
                    current := next;
                }
                else if (env==Radiation)
                {
                    actions := actions + [PatrolC];
                    current := C;
                }
            
            }

            else if(current == B)
            {
                if(env == Fine)
                {
                    actions := actions + [PatrolC, ArmUp, MastUp];
                    current := next;
                }
                else if(env == Windy)
                { 
                    actions := actions + [PatrolC, ArmDown, MastDown];
                    current := next;
                }
                else if (env==Radiation)
                {
                    actions := actions + [PatrolA];
                    current := A;
                }
            
            }

            else if(current == C || current == origin)
            {
                if(env == Fine)
                {
                    actions := actions + [PatrolA, ArmUp, MastUp];
                    current := next;
                }
                else if(env == Windy)
                { 
                    actions := actions + [PatrolA, ArmDown, MastDown];
                    current := next;
                }
            
            }
            time := time + 10;
         }
        time := time + 10;
    }
}

method getEnvironment(w:Waypoint, windspeed:int, radiation:int) returns(e:Environment)
requires windspeed >= 0; // These could be runtime checks, marked with //^
requires radiation >= 0;//^
ensures windspeed < 5 && radiation < 5 ==> e == Fine;//^
{
    if(windspeed < 5 && radiation < 5)
    {
        e := Fine;
    }
    else if (windspeed >= 5)
    {
        e := Windy;
    }
    else if (radiation >= 5)
    {
        e := Radiation;
    }

}

//windy at A
method getWind(w:Waypoint) returns (wind:int)
ensures wind >= 0; //^
ensures w==A ==> wind ==10;//^
{
    if(w==A)
    {
        wind := 10;
    }
    else{
        wind := 2;
    }
}
//radiation at B
method getRad(w:Waypoint, time:int) returns (rad:int)
requires time >= 0;//^
ensures rad >= 0;//^
ensures w==B && time <=100 ==> rad ==100 - time;//^
ensures w!=B && time <=100 ==> rad ==3;//^
{
    if(time > 100)
    {
        rad :=0;
    }
    else if (w == B && time <=100)
    {
        rad := 100 - time;
    }
    else
    {
        rad := 3;
    }
    
}

function method getnextwaypoint(w:Waypoint) :Waypoint
{
    if w ==A then B 
    else if w==B then C
    else if w==origin then A
    else A
}

//made this into modules here for readability of above code.
module Wheels{
    function method Ready():bool
    {
        true
    }
}

module Arm{
    function method Ready():bool
    {
        true
    }
}

module Mast{
    function method Ready():bool
    {
        true
    }
}
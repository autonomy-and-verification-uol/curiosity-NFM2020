//patrol A--B--C if everything is fine or if windy, but arm and mast down if windy
//dont't go where the radiation is beacuse it damages the equipment


datatype Command = PatrolA | PatrolB | PatrolC | ArmUp | ArmDown | MastUp | MastDown
datatype Environment = Windy | Radiation | Fine
datatype Waypoint = A |B | C
//should be a 'D' or 'origin'
//add a main method where environement values are assigned
// upload to repository
method CuriosityAgent(ready:bool) returns (actions: seq<Command>)
ensures ready == false ==> actions ==[];
ensures ready == true ==> |actions| > 0;
//environment returns the 3 things that are ready
//should visit all 3?
//most dangerous last?
//stop as soon as all 3 are visited
//another node: environment
{
    actions := [];
    if(ready)
    {
        var lastvisited := getcurrentwaypoint();
        var wind := getWind(lastvisited);
        var rad := getRad(lastvisited);
        var env := getEnvironment(lastvisited, wind, rad);

        if(lastvisited == A)
        {
            if(env == Fine)
            {
                actions := actions + [PatrolB, ArmUp, MastUp];
                lastvisited := B;
            }
            else if(env == Windy)
            { 
                actions := actions + [PatrolB, ArmDown, MastDown];
                lastvisited := B;
            }
            else if (env==Radiation)
            {
                actions := actions + [PatrolC];
                lastvisited := C;
            }
            
        }
        wind := getWind(lastvisited);
        rad := getRad(lastvisited);
        env := getEnvironment(lastvisited, wind, rad);

        if(lastvisited == B)
        {
            if(env == Fine)
            {
                actions := actions + [PatrolC, ArmUp, MastUp];
                lastvisited := C;
            }
            else if(env == Windy)
            { 
                actions := actions + [PatrolC, ArmDown, MastDown];
                lastvisited := C;
            }
            else if (env==Radiation)
            {
                actions := actions + [PatrolA];
                lastvisited := A;
            }
            
        }

        wind := getWind(lastvisited);
        rad := getRad(lastvisited);
        env := getEnvironment(lastvisited, wind, rad);

        if(lastvisited == C)
        {
            if(env == Fine)
            {
                actions := actions + [PatrolA, ArmUp, MastUp];
                lastvisited := A;
            }
            else if(env == Windy)
            { 
                actions := actions + [PatrolA, ArmDown, MastDown];
                lastvisited := A;
            }
            else if (env==Radiation)
            {
                actions := actions + [PatrolB];
                lastvisited := B;
            }
            
        }
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
method getRad(w:Waypoint) returns (rad:int)
ensures rad >= 0;//^
ensures w==B ==> rad ==10;//^
{
    if (w == B)
    {
        rad := 10;
    }
    else
    {
        rad := 3;
    }
    
}

method getcurrentwaypoint() returns (w:Waypoint)//helper
{
}
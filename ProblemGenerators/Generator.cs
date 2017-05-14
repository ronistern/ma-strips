using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace Planning.ProblemGenerators
{
    class Generator
    {
        public static void CreateMALogistics(string sPath, int cMinAreas, int cMaxAreas, int cMinCitiesPerArea, int cMaxCitiesPerArea, int cMincPackages, int cMaxcPackages, int cBlocksStep)
        {
            for (int cAreas = cMinAreas; cAreas <= cMaxAreas; cAreas += 1)
            {
                for (int cCitiesPerArea = cMinCitiesPerArea; cCitiesPerArea <= cMaxCitiesPerArea; cCitiesPerArea += 1)
                {
                    for (int cPackages = cMincPackages; cPackages <= cMaxcPackages; cPackages += cBlocksStep)
                    {
                        MALogistics world = new MALogistics(cPackages, cAreas, cCitiesPerArea);
                        world.WriteFactoredDomains(sPath + "/" + world.Name);
                        world.WriteFactoredProblems(sPath + "/" + world.Name);
                    }

                }
            }
        }

        public static void CreateMABlocksWorld(string sPath, int cMinArms, int cMaxArms, int cMinStacksPerArm, int cMaxStacksPerArm, int cMinBlocks, int cMaxBlocks, int cBlocksStep)
        {
            for (int cArms = cMinArms; cArms <= cMaxArms; cArms += 1)
            {
                for (int cStacks = cMinStacksPerArm; cStacks <= cMaxStacksPerArm; cStacks += 1)
                {
                    for (int cBlocks = cMinBlocks; cBlocks <= cMaxBlocks; cBlocks += cBlocksStep)
                    {
                        MABlocksWorld2 world = new MABlocksWorld2(cBlocks, cArms, cStacks);
                        world.WriteFactoredDomains(sPath + "/" + world.Name);
                        world.WriteFactoredProblems(sPath + "/" + world.Name);
                    }

                }
            }
        }
    }
}

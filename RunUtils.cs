using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading;

namespace Planning
{
    class RunUtils
    {
        private static void RunUsingProcesses(DirectoryInfo di, string sOutputPlanFile)
        {
            Program.Start = new DateTime(0);
            Program.StartHighLevelPlanning = new DateTime(0);
            Program.StartGrounding = new DateTime(0);
            Program.End = new DateTime(0);
            Program.PlanCost = -1;
            Program.PlanMakeSpan = -1;

            Console.WriteLine("Scanning directory " + di.Name);
            bool bContainsRealDirectories = false;
            int cSubs = 0;
            if (di.GetDirectories().Length != 0)
            {
                foreach (DirectoryInfo diSub in di.GetDirectories().OrderBy(d => d.Name.ToString()))
                {
                    if (!diSub.Name.ToLower().Contains("pdb"))
                    {
                        RunUsingProcesses(diSub, sOutputPlanFile);
                        bContainsRealDirectories = true;
                        cSubs++;
                    }
                }
            }
            if (!bContainsRealDirectories)
            {
                if (di.ToString().Contains("PdbFiles"))
                    return;

                Process p = new Process();
                p.StartInfo.FileName = "GPPP.exe";

                p.StartInfo.Arguments = "\"" + di.FullName + "\"";// "\"" + +"\",\"" + sOutputPlanFile + "\"";
                p.Start();
                if (!p.WaitForExit(30 * 60 * 1000))
                {
                    p.Kill();
                    p.WaitForExit();
                }
                KillPlanners();
            }
        }

        /**
         * Kills all the running planners
         **/
        public static void KillPlanners()
        {
            List<Process> lPlanningProcesses = GetPlanningProcesses();
            KillAll(lPlanningProcesses);
        }

        public static void KillAll(List<Process> l)
        {

            foreach (Process p in l)
            {
                try
                {
                    if (!p.HasExited)
                    {

                        p.Kill();
                        Thread.Sleep(40);
                        // p.WaitForExit();
                        p.Close();


                    }
                }
                catch (Exception e)
                {
                    //Console.WriteLine("*");
                }


            }


        }

        public static List<Process> GetPlanningProcesses()
        {
            List<Process> l = new List<Process>();
            foreach (Process p in Process.GetProcesses())
            {
                if (p.ProcessName.ToLower().Contains("downward") || p.ProcessName.ToLower().Contains("ff"))
                    l.Add(p);
            }
            return l;
        }
    }
}

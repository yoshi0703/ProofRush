import Problems.SmokeTest.Statement

namespace SmokeTest

theorem main_conjecture : SmokeStatement := by
  intro n
  constructor
  · omega
  · ring

end SmokeTest

import unittest

from ppci.buildfunctions import construct
from util import relpath, has_qemu, run_qemu


class EmulationTestCase(unittest.TestCase):
    """ Tests the compiler driver """

    def test_m3_bare(self):
        """ Build bare m3 binary and emulate it """
        recipe = relpath('..', 'examples', 'lm3s6965evb', 'build.xml')
        construct(recipe)
        if not has_qemu():
            self.skipTest('Not running Qemu test')
        data = run_qemu(relpath('..', 'examples', 'lm3s6965evb', 'bare.bin'))
        self.assertEqual('Hello worle', data)

    def test_a9_bare(self):
        """ Build vexpress cortex-A9 binary and emulate it """
        recipe = relpath('..', 'examples', 'realview-pb-a8', 'build.xml')
        construct(recipe)
        if not has_qemu():
            self.skipTest('Not running Qemu test')
        data = run_qemu(
            relpath('..', 'examples', 'realview-pb-a8', 'hello.bin'),
            machine='realview-pb-a8')
        self.assertEqual('Hello worle', data)

    def test_blinky(self):
        """ Compile the example for the stm32f4discovery board """
        recipe = relpath('..', 'examples', 'blinky', 'build.xml')
        construct(recipe)

    @unittest.skip('todo')
    def test_arduino(self):
        recipe = relpath('..', 'examples', 'arduino', 'build.xml')
        construct(recipe)

    def test_snake(self):
        """ Compile the snake example """
        recipe = relpath('..', 'examples', 'build.xml')
        construct(recipe)

if __name__ == '__main__':
    unittest.main()

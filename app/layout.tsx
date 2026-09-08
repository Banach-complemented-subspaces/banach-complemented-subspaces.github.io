import type { Metadata } from 'next';
import './globals.css';
import 'katex/dist/katex.min.css';
import { Navigation } from '@/components/companion';
import paper from '@/content/paper.json';
export const metadata: Metadata = {
  title: paper.manuscript.title,
  description:
    'The mathematics, exact Lean statements, and verification evidence.',
  robots: { index: true, follow: true },
  referrer: 'no-referrer',
  icons: { icon: '/favicon.svg' },
};
export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en-GB">
      <body>
        <a className="skip" href="#main">
          Skip to content
        </a>
        <header>
          <div className="header-inner">
            <a className="brand" href="/">
              Complemented subspaces<span>Paper & formalisation</span>
            </a>
            <Navigation />
          </div>
        </header>
        <main id="main">{children}</main>
        <footer>
          <span>Antonio Acuaviva · September 2026</span>
          <a href="/verification/#methodology">Formalisation & attribution</a>
        </footer>
      </body>
    </html>
  );
}

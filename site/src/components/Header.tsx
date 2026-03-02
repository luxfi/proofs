'use client'

import { Moon, Sun } from 'lucide-react'
import { useTheme } from 'next-themes'
import type { SiteConfig } from '@/config/proofs'

interface HeaderProps {
  config: SiteConfig
}

export function Header({ config }: HeaderProps) {
  const { theme, setTheme } = useTheme()

  return (
    <header className="border-b border-border/50 bg-background/80 backdrop-blur-sm sticky top-0 z-50">
      <div className="max-w-7xl mx-auto px-6 py-4">
        <div className="flex items-center justify-between">
          <div className="flex items-center gap-3">
            <Logo />
            <div>
              <h1 className="text-lg font-semibold tracking-tight">{config.name}</h1>
              <p className="text-xs text-muted-foreground">Formal Proofs</p>
            </div>
          </div>

          <div className="flex items-center gap-4">
            <nav className="hidden md:flex items-center gap-5 text-sm">
              <a
                href="https://papers.lux.network"
                className="text-muted-foreground hover:text-foreground transition-colors"
              >
                Papers
              </a>
              <a
                href="https://consensus.lux.network"
                className="text-muted-foreground hover:text-foreground transition-colors"
              >
                Consensus
              </a>
              <a
                href="https://audits.lux.network"
                className="text-muted-foreground hover:text-foreground transition-colors"
              >
                Audits
              </a>
              <a
                href={config.github}
                target="_blank"
                rel="noopener noreferrer"
                className="text-muted-foreground hover:text-foreground transition-colors"
              >
                GitHub
              </a>
            </nav>
            <button
              onClick={() => setTheme(theme === 'dark' ? 'light' : 'dark')}
              className="p-2 rounded-md text-muted-foreground hover:text-foreground hover:bg-accent transition-colors"
              aria-label="Toggle theme"
            >
              <Sun className="h-4 w-4 hidden dark:block" />
              <Moon className="h-4 w-4 block dark:hidden" />
            </button>
          </div>
        </div>
      </div>
    </header>
  )
}

function Logo() {
  return (
    <svg viewBox="0 0 100 100" className="w-7 h-7" xmlns="http://www.w3.org/2000/svg">
      <path d="M50 85 L15 25 L85 25 Z" fill="currentColor" className="text-foreground" />
    </svg>
  )
}
